use hax_lib::*;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

const BARRETT_R: i64 = 0x400000; // is 0x4000000 in the normal barrett example

const BARRETT_SHIFT: i64 = 26;

const BARRETT_MULTIPLIER: i64 = 20159;

pub(crate) const FIELD_MODULUS: i32 = 3329;

// Signed Barrett Reduction
//
// Given an input `value`, `barrett_reduce` outputs a representative `result`
// such that:
//
// - result ≡ value (mod FIELD_MODULUS)
// - the absolute value of `result` is bound as follows:
//
// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
//
// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.

#[requires(i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R)]
#[ensures(|result| {
    let valid_result = value % FIELD_MODULUS;
    result > -FIELD_MODULUS
        && result < FIELD_MODULUS
        && (result == valid_result
            || result == valid_result + FIELD_MODULUS
            || result == valid_result - FIELD_MODULUS) })]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
