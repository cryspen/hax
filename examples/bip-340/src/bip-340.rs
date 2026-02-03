//! This crate is an INSECURE prototype implementation of BIP-340 (<https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki>).
//! It is vulnerable against timing attacks.

use sha256::sha256;
use num_bigint::{self, Sign};
use num_traits::Euclid;
use hax_lib::int::*;
use hax_lib::Abstraction;

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidSecretKey,
    InvalidNonceGenerated,
    InvalidPublicKey,
    InvalidXCoordinate,
    InvalidSignature,
}

pub trait ModularArithmetic: Clone + PartialEq + Sized {
    fn modulus() -> Int;

    fn new(value: Int) -> Self;
    
    fn get_value(&self) -> &Int;
    
    fn mod_reduce(value: Int, modulus: Int) -> Int {
        let result = value.get().rem_euclid(&modulus.get());
        Int::new(result)
    }
    
    fn from_byte_seq_be(bytes: &[u8; 32]) -> Self {
        let bigint = num_bigint::BigInt::from_bytes_be(Sign::Plus, bytes);
        Self::new(Int::new(bigint))
    }
    
    fn to_byte_seq_be(&self) -> [u8; 32] {
        let bigint = self.get_value().get();
        let (_, bytes) = bigint.to_bytes_be();
        
        let mut result = [0u8; 32];
        if bytes.len() <= 32 {
            let start_idx = 32 - bytes.len();
            result[start_idx..].copy_from_slice(&bytes);
        } else {
            result.copy_from_slice(&bytes[bytes.len() - 32..]);
        }
        result
    }
    
    fn bit(&self, index: usize) -> bool {
        let byte_index = index / 8;
        let bit_index = index % 8;
        let bytes = self.to_byte_seq_be();
        if byte_index < 32 {
            (bytes[31 - byte_index] >> bit_index) & 1 == 1
        } else {
            false
        }
    }
    
    #[allow(non_snake_case)]
    fn ZERO() -> Self {
        Self::new(0u8.lift())
    }

    #[allow(non_snake_case)]
    fn ONE() -> Self {
        Self::new(1u8.lift())
    }

    #[allow(non_snake_case)]
    fn TWO() -> Self {
        Self::new(2u8.lift())
    }
    
    fn mod_add(self, other: Self) -> Self {
        let modulus = Self::modulus().get();
        let result = (self.get_value().get() + other.get_value().get()).rem_euclid(&modulus);
        Self::new(Int::new(result))
    }
    
    fn mod_sub(self, other: Self) -> Self {
        let modulus = Self::modulus().get();
        let result = (self.get_value().get() + &modulus - other.get_value().get()).rem_euclid(&modulus);
        Self::new(Int::new(result))
    }
    
    fn mod_mul(self, other: Self) -> Self {
        let modulus = Self::modulus().get();
        let result = (self.get_value().get() * other.get_value().get()).rem_euclid(&modulus);
        Self::new(Int::new(result))
    }

    fn from_bytes_strict(b: [u8; 32]) -> Option<Self> {
        let s = num_bigint::BigInt::from_bytes_be(Sign::Plus, &b);
        let max_value = Self::modulus().get();
        
        if s >= max_value {
            None
        } else {
            Some(Self::new(Int::new(s)))
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct FieldElement {
    value: Int,
}

impl ModularArithmetic for FieldElement {
    fn modulus() -> Int {
        int!(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
    }
    
    fn new(value: Int) -> Self {
        let reduced = Self::mod_reduce(value, Self::modulus());
        Self { value: reduced }
    }
    
    fn get_value(&self) -> &Int {
        &self.value
    }
}

impl FieldElement {
    pub fn pow_self(&self, exp: FieldElement) -> FieldElement {
        let modulus = Self::modulus().get();
        let base = self.value.get();
        let exponent = exp.value.get();
        let result = base.modpow(&exponent, &modulus);
        Self {
            value: Int::new(result),
        }
    }
}

macro_rules! impl_arithmetic_ops {
    ($type:ty) => {
        impl std::ops::Add for $type {
            type Output = Self;
            fn add(self, other: Self) -> Self {
                self.mod_add(other)
            }
        }

        impl std::ops::Sub for $type {
            type Output = Self;
            fn sub(self, other: Self) -> Self {
                self.mod_sub(other)
            }
        }

        impl std::ops::Mul for $type {
            type Output = Self;
            fn mul(self, other: Self) -> Self {
                self.mod_mul(other)
            }
        }
    };
}

impl_arithmetic_ops!(FieldElement);

impl std::ops::Rem for FieldElement {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        let result = self.value.get().rem_euclid(&other.value.get());
        FieldElement { value: Int::new(result) }
    }
}

#[derive(Clone, PartialEq)]
pub struct Scalar {
    value: Int,
}

impl ModularArithmetic for Scalar {
    fn modulus() -> Int {
        int!(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
    }
    
    fn new(value: Int) -> Self {
        let reduced = Self::mod_reduce(value, Self::modulus());
        Self { value: reduced }
    }
    
    fn get_value(&self) -> &Int {
        &self.value
    }
}

impl_arithmetic_ops!(Scalar);

fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut result = String::new();
    for byte in bytes {
        result.push_str(&format!("{:02x}", byte));
    }
    result
}

macro_rules! impl_debug {
    ($type:ty, $name:expr) => {
        impl std::fmt::Debug for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", $name, bytes_to_hex(&self.to_byte_seq_be()))
            }
        }
    };
}

impl_debug!(FieldElement, "FieldElement");
impl_debug!(Scalar, "Scalar");

pub type AffinePoint = (FieldElement, FieldElement);

#[derive(Debug, Clone)]
pub enum Point {
    Affine(AffinePoint),
    AtInfinity,
}

pub fn finite(p: Point) -> Option<AffinePoint> {
    match p {
        Point::Affine(p) => Some(p),
        Point::AtInfinity => None,
    }
}

pub fn x(p: &AffinePoint) -> FieldElement {
    let (x, _) = p;
    x.clone()
}

pub fn y(p: &AffinePoint) -> FieldElement {
    let (_, y) = p;
    y.clone()
}

pub fn has_even_y(p: AffinePoint) -> bool {
    y(&p) % FieldElement::TWO() == FieldElement::ZERO()
}

fn sqrt(y: FieldElement) -> Option<FieldElement> {
    // This is the field element equal to (p+1)/4.
    let p1_4_bytes = [
        0x3Fu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xBFu8, 0xFFu8, 0xFFu8, 0x0Cu8
    ];
    let p1_4 = FieldElement::from_byte_seq_be(&p1_4_bytes);
    let x = y.pow_self(p1_4);
    if x.pow_self(FieldElement::TWO()) == y {
        Some(x)
    } else {
        None
    }
}

pub fn lift_x(x: FieldElement) -> Result<AffinePoint, Error> {
    let one = FieldElement::ONE();
    let two = FieldElement::TWO();
    let three = FieldElement::new(3u128.lift());
    let seven = FieldElement::new(7u128.lift());
    let y_sq = x.pow_self(three) + seven;
    let mut y = sqrt(y_sq).ok_or(Error::InvalidXCoordinate)?;
    if y.clone() % two == one {
        y = FieldElement::ZERO() - y;
    }
    Ok((x, y))
}

fn compute_lam(p1: AffinePoint, p2: AffinePoint) -> FieldElement {
    let three = FieldElement::new(3u128.lift());
    if p1 != p2 {
        (y(&p2) - y(&p1)) * (x(&p2) - x(&p1)).pow_self(FieldElement::ZERO() - FieldElement::TWO())
    } else {
        three * x(&p1) * x(&p1) * (FieldElement::TWO() * y(&p1)).pow_self(FieldElement::ZERO() - FieldElement::TWO())
    }
}

pub fn point_add(p1: Point, p2: Point) -> Point {
    if finite(p1.clone()).is_none() { return p2 }
    if finite(p2.clone()).is_none() { return p1 }

    let p1_affine = finite(p1).unwrap();
    let p2_affine = finite(p2).unwrap();
    if !((x(&p1_affine) == x(&p2_affine)) && (y(&p1_affine) != y(&p2_affine))) {
        let lam = compute_lam(p1_affine.clone(), p2_affine.clone());
        let x3 = lam.clone() * lam.clone() - x(&p1_affine) - x(&p2_affine);
        return Point::Affine((x3.clone(), lam * (x(&p1_affine) - x3) - y(&p1_affine)));
    }
    Point::AtInfinity
}

pub fn point_mul(s: Scalar, p: Point) -> Point {
    let mut p = p;
    let mut q = Point::AtInfinity;
    for i in 0..256 {
        if s.bit(i) {
            q = point_add(q, p.clone());
        }
        p = point_add(p.clone(), p);
    }
    q
}

pub fn point_mul_base(s: Scalar) -> Point {
    let gx_bytes = [
        0x79u8, 0xBEu8, 0x66u8, 0x7Eu8, 0xF9u8, 0xDCu8, 0xBBu8, 0xACu8,
        0x55u8, 0xA0u8, 0x62u8, 0x95u8, 0xCEu8, 0x87u8, 0x0Bu8, 0x07u8,
        0x02u8, 0x9Bu8, 0xFCu8, 0xDBu8, 0x2Du8, 0xCEu8, 0x28u8, 0xD9u8,
        0x59u8, 0xF2u8, 0x81u8, 0x5Bu8, 0x16u8, 0xF8u8, 0x17u8, 0x98u8
    ];
    let gy_bytes = [
        0x48u8, 0x3Au8, 0xDAu8, 0x77u8, 0x26u8, 0xA3u8, 0xC4u8, 0x65u8,
        0x5Du8, 0xA4u8, 0xFBu8, 0xFCu8, 0x0Eu8, 0x11u8, 0x08u8, 0xA8u8,
        0xFDu8, 0x17u8, 0xB4u8, 0x48u8, 0xA6u8, 0x85u8, 0x54u8, 0x19u8,
        0x9Cu8, 0x47u8, 0xD0u8, 0x8Fu8, 0xFBu8, 0x10u8, 0xD4u8, 0xB8u8
    ];
    let g = Point::Affine((
        FieldElement::from_byte_seq_be(&gx_bytes),
        FieldElement::from_byte_seq_be(&gy_bytes),
    ));
    point_mul(s, g)
}

pub type Bytes32 = [u8; 32];
pub type SecretKey = Bytes32;
pub type PublicKey = Bytes32;
pub type Message = Bytes32;
pub type AuxRand = Bytes32;
pub type Signature = [u8; 64];

pub fn tagged_hash(tag: &[u8], msg: &[u8]) -> Bytes32 {
    let tag_hash = sha256(tag);
    let mut combined = Vec::new();
    combined.extend_from_slice(&tag_hash);
    combined.extend_from_slice(&tag_hash);
    combined.extend_from_slice(msg);
    sha256(&combined)
}

// "BIP0340/aux"
const BIP0340_AUX: &[u8] = &[
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x61u8, 0x75u8, 0x78u8,
];

pub fn hash_aux(aux_rand: AuxRand) -> Bytes32 {
    tagged_hash(BIP0340_AUX, &aux_rand)
}

// "BIP0340/nonce"
const BIP0340_NONCE: &[u8] = &[
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8,
    0x65u8,
];

pub fn hash_nonce(rand: Bytes32, pubkey: Bytes32, msg: Message) -> Bytes32 {
    let mut c = Vec::new();
    c.extend_from_slice(&rand);
    c.extend_from_slice(&pubkey);
    c.extend_from_slice(&msg);
    tagged_hash(BIP0340_NONCE, &c)
}

// "BIP0340/challenge"
const BIP0340_CHALLENGE: &[u8] = &[
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x63u8, 0x68u8, 0x61u8, 0x6cu8,
    0x6cu8, 0x65u8, 0x6eu8, 0x67u8, 0x65u8,
];

pub fn hash_challenge(rx: Bytes32, pubkey: Bytes32, msg: Bytes32) -> Bytes32 {
    let mut c = Vec::new();
    c.extend_from_slice(&rx);
    c.extend_from_slice(&pubkey);
    c.extend_from_slice(&msg);
    tagged_hash(BIP0340_CHALLENGE, &c)
}

pub fn seckey_scalar_from_bytes(b: Bytes32) -> Option<Scalar> {
    let s = Scalar::from_bytes_strict(b)?;
    if s == Scalar::ZERO() {
        None
    } else {
        Some(s)
    }
}

fn xor_bytes(b0: Bytes32, b1: Bytes32) -> Bytes32 {
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = b0[i] ^ b1[i];
    }
    result
}

pub type PubkeyGenResult = Result<PublicKey, Error>;
pub fn pubkey_gen(seckey: SecretKey) -> PubkeyGenResult {
    let d0 = seckey_scalar_from_bytes(seckey).ok_or(Error::InvalidSecretKey)?;
    let p = finite(point_mul_base(d0)).unwrap();
    Ok(x(&p).to_byte_seq_be())
}

pub type SignResult = Result<Signature, Error>;
pub fn sign(msg: Message, seckey: SecretKey, aux_rand: AuxRand) -> SignResult {
    let d0 = seckey_scalar_from_bytes(seckey).ok_or(Error::InvalidSecretKey)?;
    let p = finite(point_mul_base(d0.clone())).unwrap();
    let d = if has_even_y(p.clone()) {
        d0
    } else {
        Scalar::ZERO() - d0
    };
    let t = xor_bytes(d.to_byte_seq_be(), hash_aux(aux_rand));
    let k0 = Scalar::from_byte_seq_be(&hash_nonce(t, x(&p).to_byte_seq_be(), msg));
    if k0 == Scalar::ZERO() {
        // This happens only with negligible probability
        return Err(Error::InvalidNonceGenerated);
    }
    let r = finite(point_mul_base(k0.clone())).unwrap();
    let k = if has_even_y(r.clone()) {
        k0
    } else {
        Scalar::ZERO() - k0
    };
    let e = Scalar::from_byte_seq_be(&hash_challenge(
        x(&r).to_byte_seq_be(),
        x(&p).to_byte_seq_be(),
        msg,
    ));
    let mut sig = [0u8; 64];
    let r_bytes = x(&r).to_byte_seq_be();
    let s_bytes = (k + e * d).to_byte_seq_be();
    sig[0..32].copy_from_slice(&r_bytes);
    sig[32..64].copy_from_slice(&s_bytes);
    
    verify(msg, x(&p).to_byte_seq_be(), sig)?;
    Ok(sig)
}

pub type VerificationResult = Result<(), Error>;
pub fn verify(msg: Message, pubkey: PublicKey, sig: Signature) -> VerificationResult {
    let p_x = FieldElement::from_bytes_strict(pubkey).ok_or(Error::InvalidPublicKey)?;
    let p = lift_x(p_x)?;
    let r_bytes: [u8; 32] = sig[0..32].try_into().unwrap();
    let s_bytes: [u8; 32] = sig[32..64].try_into().unwrap();
    let r = FieldElement::from_bytes_strict(r_bytes).ok_or(Error::InvalidSignature)?;
    let s = Scalar::from_bytes_strict(s_bytes).ok_or(Error::InvalidSignature)?;

    let e = Scalar::from_byte_seq_be(&hash_challenge(r_bytes, x(&p).to_byte_seq_be(), msg));
    let r_p = finite(point_add(
        point_mul_base(s),
        point_mul(Scalar::ZERO() - e, Point::Affine(p)),
    ))
    .ok_or(Error::InvalidSignature)?;
    
    if !has_even_y(r_p.clone()) || (x(&r_p) != r) {
        Err(Error::InvalidSignature)
    } else {
        Ok(())
    }
}
