//! # 32-bit Addition with Carry (ADC)
//!
//! This example demonstrates formal verification of a 32-bit
//! addition-with-carry (ADC) operation using the hax toolchain and
//! Lean 4's `bv_decide` bit-vector decision procedure.
//!
//! ## What is ADC?
//!
//! Addition with carry (ADC) is a fundamental building block in
//! multi-precision (bignum) arithmetic. When adding large numbers
//! represented as arrays of 32-bit "limbs", each limb addition may
//! overflow. The ADC operation captures this overflow as a carry-out
//! bit, which feeds into the next limb addition.
//!
//! For example, to add two 128-bit numbers stored as four 32-bit limbs:
//!
//! ```text
//!   (sum0, c0) = adc(a[0], b[0], 0)
//!   (sum1, c1) = adc(a[1], b[1], c0)
//!   (sum2, c2) = adc(a[2], b[2], c1)
//!   (sum3, c3) = adc(a[3], b[3], c2)
//! ```
//!
//! ## Verification approach
//!
//! The precondition and postcondition are expressed as plain Rust
//! functions (`adc_precondition`, `adc_postcondition`) for documentation.
//! A correctness theorem is embedded via `#[hax_lib::lean::after(...)]`
//! using a Hoare triple with pure Lean propositions (not the monadic
//! Rust functions), since `bv_decide` requires pure BitVec goals.
//!
//! The proof is fully automated using the tactics from Hax:
//!
//!   1. `hax_mvcgen` — generates pure verification conditions from
//!      the monadic function body using the `bv` specset lemmas.
//!   2. `simp only [hax_bv_decide]` — normalizes the VCs using
//!      hax's bit-vector simplification lemmas.
//!   3. `bv_decide` — Lean's bit-blasting decision procedure
//!      automatically verifies the remaining BitVec goals.
//!
//! The key property verified:
//!
//! ```text
//!   a + b + carry_in == sum + carry_out * 2^32
//! ```
//!
//! where the left-hand side is computed in `u64` to avoid overflow.

/// Precondition: the input carry must be 0 or 1 (a single bit).
///
/// This function documents the precondition and is extracted to Lean,
/// but the proof theorem states the precondition as a pure Lean
/// proposition (`carry_in ≤ 1`) rather than using this monadic function.
fn adc_precondition(carry_in: u32) -> bool {
    carry_in <= 1
}

/// Postcondition: the 64-bit sum `a + b + carry_in` is correctly
/// represented as `sum + carry_out * 2^32`.
///
/// We verify two properties:
///   1. `carry_out` is 0 or 1 (it is a single bit).
///   2. The full equation holds: the wide sum equals the split result.
///
/// Like `adc_precondition`, this documents the postcondition but the
/// proof uses pure Lean propositions instead of this monadic function.
fn adc_postcondition(a: u32, b: u32, carry_in: u32, sum: u32, carry_out: u32) -> bool {
    carry_out <= 1
        && (a as u64 + b as u64 + carry_in as u64)
            == (sum as u64 + ((carry_out as u64) << 32u64))
}

/// 32-bit addition with carry.
///
/// Computes `a + b + carry_in` where `carry_in` is 0 or 1.
/// Returns `(sum, carry_out)` where:
///   - `sum` is the lower 32 bits of the result
///   - `carry_out` is 1 if the addition overflowed, 0 otherwise
///
/// The computation widens operands to `u64` to avoid overflow, then
/// splits the 64-bit result back into 32-bit values.
///
/// # Verification
///
/// The `#[hax_lib::lean::after(...)]` attribute embeds a Lean 4
/// theorem directly after the extracted function definition. This
/// theorem states: given the precondition (carry_in is 0 or 1),
/// the function satisfies the postcondition (the full sum equation
/// holds and carry_out is 0 or 1).
///
/// The proof uses:
///   1. `hax_mvcgen` — to generate pure verification conditions
///      from the monadic function body.
///   2. `simp only [hax_bv_decide]` — to normalize with bv specset
///      lemmas.
///   3. `bv_decide` — Lean's bit-blasting procedure to
///      automatically verify the remaining BitVec goals.
#[hax_lib::lean::after(
    // The specification is stated with pure Lean propositions (not through the
    // monadic adc_precondition/adc_postcondition Rust functions), so that
    // bv_decide can reason about the BitVec properties directly.
    "
set_option maxHeartbeats 1000000 in
set_option hax_mvcgen.specset \"bv\" in
theorem adc_u32_spec (a b carry_in : u32) :
  ⦃ ⌜ carry_in ≤ 1 ⌝ ⦄
  lean_adc.adc_u32 a b carry_in
  ⦃ ⇓ ⟨sum, carry_out⟩ =>
    ⌜ carry_out ≤ 1 ∧
      UInt32.toUInt64 a + UInt32.toUInt64 b + UInt32.toUInt64 carry_in =
        UInt32.toUInt64 sum + (UInt32.toUInt64 carry_out <<< (32 : UInt64)) ⌝ ⦄
:= by
  hax_mvcgen [lean_adc.adc_u32]
    <;> (try simp only [hax_bv_decide] at *)
    <;> bv_decide (timeout := 90)
"
)]
pub fn adc_u32(a: u32, b: u32, carry_in: u32) -> (u32, u32) {
    // Widen to u64 so the addition cannot overflow.
    let wide: u64 = a as u64 + b as u64 + carry_in as u64;
    // Extract the lower 32 bits as the sum.
    let sum: u32 = wide as u32;
    // Extract bit 32 as the carry-out (0 or 1).
    let carry_out: u32 = (wide >> 32u64) as u32;
    (sum, carry_out)
}
