//! Equivalence tests for `core::ops::*`.
//!
//! Mirrors the proptest block in `core-models/src/core/ops.rs`, which
//! has exactly two cases:
//!   - `arith::AddAssign::add_assign` on `u8` (with `x, y` constrained
//!     to `0..128` so the sum cannot overflow), and
//!   - `arith::SubAssign::sub_assign` on `u8` (when `x >= y`).
//!
//! On the Rust side we use the `+=` / `-=` operators (which dispatch
//! through `AddAssign` / `SubAssign`); on the Lean side Aeneas
//! extracts the same operations against the model's impls.
//!
//! All values are kept inside the precondition ranges (no overflow,
//! lhs >= rhs).

use rust_lean_test_macro::rust_lean_test;

// =============================================================================
// AddAssign on u8 (precondition: x + y <= u8::MAX, mirrored from
// the proptest's `0u8..128` range bound on both operands)
// =============================================================================

#[rust_lean_test]
pub fn test_add_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x += 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_zero_plus_one() -> bool {
    let mut x: u8 = 0;
    x += 1u8;
    x == 1u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_mid() -> bool {
    let mut x: u8 = 42;
    x += 58u8;
    x == 100u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_boundary() -> bool {
    // The proptest constrains both operands to `0..128`, so 127 + 127
    // is the largest sum we can express (= 254, just under u8::MAX).
    let mut x: u8 = 127;
    x += 127u8;
    x == 254u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_lhs_zero() -> bool {
    let mut x: u8 = 0;
    x += 127u8;
    x == 127u8
}

// =============================================================================
// SubAssign on u8 (precondition: lhs >= rhs)
// =============================================================================

#[rust_lean_test]
pub fn test_sub_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x -= 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_self() -> bool {
    let mut x: u8 = 42;
    x -= 42u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_mid() -> bool {
    let mut x: u8 = 100;
    x -= 42u8;
    x == 58u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_zero() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 0u8;
    x == u8::MAX
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_one() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 1u8;
    x == 254u8
}
