use hax_lib as hax;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 0x4000000; // 2^26

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
const BARRETT_MULTIPLIER: i64 = 20159;

pub(crate) const FIELD_MODULUS: i32 = 3329;

/// Signed Barrett Reduction
///
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
///
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
///
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
///
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS &&
                   result % FIELD_MODULUS == value % FIELD_MODULUS)]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    // assert!(9223372036854775807 - (BARRETT_R >> 1) > t);
    let t = t + (BARRETT_R >> 1);

    let quotient = t >> BARRETT_SHIFT;
    // assert!(quotient <= 2147483647_i64 || quotient >= -2147483648_i64);
    let quotient = quotient as i32;

    // assert!(((quotient as i64) * (FIELD_MODULUS as i64)) < 9223372036854775807);
    let sub = quotient * FIELD_MODULUS;

    hax::fstar!(r"Math.Lemmas.cancel_mul_mod (v $quotient) 3329");

    value - sub
}
