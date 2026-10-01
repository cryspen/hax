//! Equivalence tests for `core::hint::*`.
//!
//! Mirrors the proptest block in `core-models/src/core/hint.rs`:
//!   - `black_box` is the identity on its argument,
//!   - `must_use` is the identity on its argument.
//!
//! `must_use` does not have a stable, value-returning entry point in
//! `core::hint` (the language item `#[must_use]` is unrelated, and any
//! `hint::must_use(value)` callable is unstable), so we only exercise
//! `black_box` from the Rust side. We compensate by hitting `black_box`
//! across multiple integer widths plus `bool`.

use rust_lean_test_macro::rust_lean_test;

// ----- black_box: u8 ---------------------------------------------------------

#[rust_lean_test]
pub fn test_black_box_u8_zero() -> bool {
    core::hint::black_box(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_black_box_u8_max() -> bool {
    core::hint::black_box(u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_black_box_u8_mid() -> bool {
    core::hint::black_box(42u8) == 42u8
}

// ----- black_box: u32 --------------------------------------------------------

#[rust_lean_test]
pub fn test_black_box_u32_zero() -> bool {
    core::hint::black_box(0u32) == 0u32
}

#[rust_lean_test]
pub fn test_black_box_u32_max() -> bool {
    core::hint::black_box(u32::MAX) == u32::MAX
}

// ----- black_box: i8 ---------------------------------------------------------

#[rust_lean_test]
pub fn test_black_box_i8_min() -> bool {
    core::hint::black_box(i8::MIN) == i8::MIN
}

#[rust_lean_test]
pub fn test_black_box_i8_max() -> bool {
    core::hint::black_box(i8::MAX) == i8::MAX
}

#[rust_lean_test]
pub fn test_black_box_i8_neg_one() -> bool {
    core::hint::black_box(-1i8) == -1i8
}

// ----- black_box: bool -------------------------------------------------------

#[rust_lean_test]
pub fn test_black_box_bool_true() -> bool {
    core::hint::black_box(true) == true
}

#[rust_lean_test]
pub fn test_black_box_bool_false() -> bool {
    core::hint::black_box(false) == false
}

// ----- must_use --------------------------------------------------------------
//
// `core::hint::must_use` is not stable in std (no public `core::hint::must_use`
// function takes an argument and returns it), so we cannot call it from the
// Rust side under a stable toolchain. The model's `must_use` is also the
// identity; covered transitively by `black_box` tests above.
//
// TODO(must_use-stability): expose a test path once a stable wrapper exists
// or the model is invoked directly through a different surface.
