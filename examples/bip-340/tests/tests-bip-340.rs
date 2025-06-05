use bip_340::*;
use serde::{Deserialize, Serialize};
use quickcheck::QuickCheck;

/* The cases.json was produced from the test vectors with the following command:

     curl -s https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv \
       | python -c 'import csv, json, sys; print(json.dumps([dict(r) for r in csv.DictReader(sys.stdin)]))' \
       | jq \
       | sed -e 's/secret key/secret_key/' -e 's/public key/public_key/' -e 's/verification result/verification_result/'

   The SHA256 digest of the test vectors produced with

     curl -s https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv \
     | sha256sum

   was a17adbd2c19032ddc12e63b5f35d5224a9295e9f82397d2632a301696b3cac9f.
*/

#[derive(Debug, Deserialize, Serialize)]
struct CasesTestVector {
    index: String,
    secret_key: String,
    public_key: String,
    aux_rand: String,
    message: String,
    signature: String,
    verification_result: String,
}

impl CasesTestVector {
    fn from_file(path: &str) -> Vec<Self> {
        let contents = std::fs::read_to_string(path).expect("Failed to read test vector file");
        serde_json::from_str(&contents).expect("Failed to parse test vector JSON")
    }
}

trait FromHex: Sized {
    fn from_hex(hex_str: &str) -> Self;
}
impl<const N: usize> FromHex for [u8; N] {
    fn from_hex(hex_str: &str) -> Self {
        hex::decode(hex_str).unwrap().try_into().unwrap()
    }
}

#[test]
fn test_invalid_secret() {
    let sk = SecretKey::from_hex("0000000000000000000000000000000000000000000000000000000000000000");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140");
    assert!(pubkey_gen(sk).is_ok());
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
}

#[test]
fn test_vectors() {
    let v = CasesTestVector::from_file("tests/cases.json");
    for t in v {
        let pk = PublicKey::from_hex(&t.public_key);
        let sig = Signature::from_hex(&t.signature);
        let msg = Message::from_hex(&t.message);
        if !t.secret_key.is_empty() {
            let sk = SecretKey::from_hex(&t.secret_key);
            let pk2 = pubkey_gen(sk).unwrap();
            assert_eq!(pk, pk2);
            let aux_rand = AuxRand::from_hex(&t.aux_rand);
            let sig2 = sign(msg, sk, aux_rand).unwrap();
            assert_eq!(sig, sig2);
        }
        let result = t.verification_result == "TRUE";
        assert_eq!(verify(msg, pk, sig).is_ok(), result);
    }
}

fn to_bytes(val: (u128, u128)) -> [u8; 32] {
    let (a, b) = val;
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&b.to_le_bytes());
    out[16..].copy_from_slice(&a.to_le_bytes());
    out
}

#[test]
fn test_sign_verify() {
    fn test_q(msg: (u128, u128), sk: (u128, u128), aux_rand: (u128, u128)) -> bool {
        let msg = to_bytes(msg);
        let sk = to_bytes(sk);
        let pk_res = pubkey_gen(sk);
        if pk_res.is_err() {
            // if there's an error, the secret key is invalid and we don't need
            // to try signing
            return true;
        }
        let aux_rand = to_bytes(aux_rand);
        // sign also verifies the resulting signature
        sign(msg, sk, aux_rand).unwrap();
        true
    }
    QuickCheck::new()
        .tests(12)
        .quickcheck(test_q as fn((u128, u128), (u128, u128), (u128, u128)) -> bool);
}
