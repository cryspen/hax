/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_R: i64 = 0x400000; // is 0x4000000 in the normal barrett example

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_SHIFT: i64 = 26;

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_MULTIPLIER: i64 = 20159;

#[hax_lib::lean::before("@[simp, spec]")]
pub(crate) const FIELD_MODULUS: i32 = 3329;

fn barrett_reduce_precondition(value: FieldElement) -> bool {
    i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R
}

fn barret_reduce_postcondition(value: FieldElement, result: FieldElement) -> bool {
    let valid_result = value % FIELD_MODULUS;
    result > -FIELD_MODULUS
        && result < FIELD_MODULUS
        && (result == valid_result
            || result == valid_result + FIELD_MODULUS
            || result == valid_result - FIELD_MODULUS)
}

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
#[hax_lib::lean::after(
  // This specification theorem will be inserted after the function definition
  // in the extracted Lean code:
    "
set_option maxHeartbeats 1000000 in
-- quite computation intensive
theorem barrett_spec (value: i32) :
  ⦃ ⌜ Lean_barrett.barrett_reduce_precondition (value) = pure true ⌝ ⦄
  Lean_barrett.barrett_reduce value
  ⦃ ⇓ r => ⌜ Lean_barrett.barret_reduce_postcondition value r = pure true⌝ ⦄
:= by
  -- Unfold all auxiliary functions:
  unfold
    Lean_barrett.barrett_reduce Lean_barrett.barrett_reduce_precondition
    Lean_barrett.barret_reduce_postcondition
    Lean_barrett.FIELD_MODULUS Lean_barrett.BARRETT_R
    Lean_barrett.BARRETT_MULTIPLIER Lean_barrett.BARRETT_SHIFT at *
  -- Invoke bit blasting:
  hax_bv_decide (timeout := 90)
"
)]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
