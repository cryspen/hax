//! # 32-bit Addition with Carry (ADC)
//!
//! This example demonstrates formal verification of a 32-bit
//! addition-with-carry (ADC) operation using the hax toolchain: the Rust
//! function is extracted to Lean and proved correct in
//! `proofs/lean/Adc/Proofs/Proofs.lean`.
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
//! The precondition and postcondition are attached to `adc_u32` with
//! `#[hax_lib::requires(..)]` and `#[hax_lib::ensures(..)]`. The Lean
//! backend turns them into a specification `adc_u32.spec`
//! in the generated `Extraction/Specs.lean`, proved correct in 
//! `proofs/lean/Adc/Proofs/Proofs.lean`.
//!
//! The proof uses `hax_mvcgen` to generate the verification conditions, which in turn are
//! discharged using `simp`, `grind`, and `scalar_tac`.
//!
//! The key property verified:
//!
//! ```text
//!   a + b + carry_in == sum + carry_out * 2^32
//! ```
//!
//! where the left-hand side is computed in `u64` to avoid overflow.

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
/// The precondition (`carry_in` is 0 or 1) and postcondition (the wide sum
/// `a + b + carry_in` equals `sum + carry_out * 2^32`, and `carry_out` is 0
/// or 1) are attached below with `#[hax_lib::requires]` / `#[hax_lib::ensures]`.
#[hax_lib::requires(carry_in <= 1)]
#[hax_lib::ensures(|result| {
    let (sum, carry_out) = result;
    carry_out <= 1
        && (a as u64 + b as u64 + carry_in as u64)
            == (sum as u64 + ((carry_out as u64) << 32u64))
})]
pub fn adc_u32(a: u32, b: u32, carry_in: u32) -> (u32, u32) {
    // Widen to u64 so the addition cannot overflow.
    let wide: u64 = a as u64 + b as u64 + carry_in as u64;
    // Extract the lower 32 bits as the sum.
    let sum: u32 = wide as u32;
    // Extract bit 32 as the carry-out (0 or 1).
    let carry_out: u32 = (wide >> 32u64) as u32;
    (sum, carry_out)
}
