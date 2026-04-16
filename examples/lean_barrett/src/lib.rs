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

fn barrett_reduce_precondition(value: FieldElement) -> bool {
    i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R
}

fn barrett_reduce_postcondition(value: FieldElement, result: FieldElement) -> bool {
    let valid_result = value % FIELD_MODULUS;
    result > -FIELD_MODULUS
        && result < FIELD_MODULUS
        && (result == valid_result
            || result == valid_result + FIELD_MODULUS
            || result == valid_result - FIELD_MODULUS)
}

pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}

// A theorem stating that Barrett meets its post-condition, given its pre-condition.
// In the next iteration, this theorem would be auto-generated, with a sorry proof.
#[hax_lib::lean::replace(
    "
set_option maxHeartbeats 1000000 in
-- quite computation intensive
theorem barrett_spec (value: i32) :
  ⦃ ⌜ barrett_reduce_precondition (value) = pure true ⌝ ⦄
  barrett_reduce value
  ⦃ ⇓ r => ⌜ barrett_reduce_postcondition value r = pure true⌝ ⦄
:= by
  -- Unfold all auxiliary functions:
  unfold
    barrett_reduce barrett_reduce_precondition
    barrett_reduce_postcondition
    FIELD_MODULUS BARRETT_R
    BARRETT_MULTIPLIER BARRETT_SHIFT at *
  -- Invoke bit blasting:
  hax_bv_decide (timeout := 90)
"
)]
pub fn theorem() {}
