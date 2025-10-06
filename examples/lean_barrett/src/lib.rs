use hax_lib as hax;
use hax_lib::lean;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i32;

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_R: i64 = 0x40000; // is 0x4000000 in the normal barrett example

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_SHIFT: i64 = 26;

#[hax_lib::lean::before("@[simp, spec]")]
const BARRETT_MULTIPLIER: i64 = 20159;

#[hax_lib::lean::before("@[simp, spec]")]
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
#[hax::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax::ensures(|result| {
  let valid_result = value % FIELD_MODULUS;
  result > -FIELD_MODULUS
  && result < FIELD_MODULUS
  && (result == valid_result ||
      result == valid_result + FIELD_MODULUS ||
      result == valid_result - FIELD_MODULUS)
})]
#[hax_lib::lean::before("@[simp, spec]")]
#[hax_lib::lean::after(
    "
theorem barrett_spec (value: i32) :
  ⦃ ⌜ Lean_barrett.__4.requires (value) = pure true ⌝ ⦄
  (do
    let result ← Lean_barrett.barrett_reduce value;
    Lean_barrett.__5.ensures value result)
  ⦃ ⇓ post => ⌜post = true⌝ ⦄
:= by
  open Spec.BV in mvcgen [Lean_barrett.__5.ensures] <;> simp at *
  hax_bv_decide
  simp [Int32.eq_iff_toBitVec_eq,
        Int32.lt_iff_toBitVec_slt,
        Int64.le_iff_toBitVec_sle,
        ] at *
  expose_names; have ⟨ _ , _ ⟩ := h_1 ; clear h_1
  generalize Int32.toBitVec value = bv_value at * ; clear value
  bv_decide (config := {timeout := 120})
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
