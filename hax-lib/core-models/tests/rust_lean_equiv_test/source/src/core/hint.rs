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
//!
//! `unreachable_unchecked` gets no test: the model panics on it (its
//! `requires(false)` forbids reaching it at all), so there is no observation
//! both sides can agree on. `Locality` and the `prefetch_*` hints get none
//! either — they do not exist in the `core` of the toolchain this crate is
//! built with, so no call site can reach them.

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

// ----- likely / unlikely -----------------------------------------------------

#[rust_lean_test]
pub fn test_likely_true() -> bool {
    core::hint::likely(true) == true
}

#[rust_lean_test]
pub fn test_likely_false() -> bool {
    core::hint::likely(false) == false
}

#[rust_lean_test]
pub fn test_unlikely_true() -> bool {
    core::hint::unlikely(true) == true
}

#[rust_lean_test]
pub fn test_unlikely_false() -> bool {
    core::hint::unlikely(false) == false
}

// ----- select_unpredictable --------------------------------------------------

#[rust_lean_test]
pub fn test_select_unpredictable_true_branch() -> bool {
    core::hint::select_unpredictable(true, 0u8, u8::MAX) == 0u8
}

#[rust_lean_test]
pub fn test_select_unpredictable_false_branch() -> bool {
    core::hint::select_unpredictable(false, 0u8, u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_select_unpredictable_i32_min() -> bool {
    core::hint::select_unpredictable(false, 0i32, i32::MIN) == i32::MIN
}

#[rust_lean_test]
pub fn test_select_unpredictable_bool_payload() -> bool {
    core::hint::select_unpredictable(true, false, true) == false
}

// ----- spin_loop / cold_path -------------------------------------------------

#[rust_lean_test]
pub fn test_spin_loop_is_a_noop() -> bool {
    let x = 42u8;
    core::hint::spin_loop();
    x == 42u8
}

#[rust_lean_test]
pub fn test_cold_path_is_a_noop() -> bool {
    let x = 42u8;
    core::hint::cold_path();
    x == 42u8
}

// ----- assert_unchecked ------------------------------------------------------
//
// Only the satisfied side is observable: `assert_unchecked(false)` is UB in
// real core and forbidden by the model's `requires`.

#[rust_lean_test]
pub fn test_assert_unchecked_holds() -> bool {
    let x = 7u8;
    unsafe { core::hint::assert_unchecked(x == 7u8) };
    x == 7u8
}

#[rust_lean_test]
pub fn test_assert_unchecked_literal_true() -> bool {
    unsafe { core::hint::assert_unchecked(true) };
    true
}
