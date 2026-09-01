//! Equivalence tests for `alloc::boxed::Box::*`.
//!
//! The model in `alloc/src/lib.rs` makes `Box::new(v)` the identity (hax
//! erases boxes), so on the Lean side `Box<T>` is `T`. The Rust side still
//! constructs a real `Box`, so dereferencing `*b` and reborrowing `&**b`
//! both have to agree with the model.
//!
//! The cases below are hand-picked to cover construction, single-deref,
//! double-deref via a reborrow, and the associated functions the model
//! provides (`new_in`, `into_inner`, `into_boxed_slice`, `map`).

use crate::helpers::Bumped;
use rust_lean_test_macro::rust_lean_test;
use std::alloc::Global;

// ----- Box::new + single deref ----------------------------------------------

#[rust_lean_test]
pub fn test_box_new_deref_zero() -> bool {
    let b: Box<u8> = Box::new(0);
    *b == 0
}

#[rust_lean_test]
pub fn test_box_new_deref_max_u8() -> bool {
    let b: Box<u8> = Box::new(u8::MAX);
    *b == u8::MAX
}

#[rust_lean_test]
pub fn test_box_new_deref_mid_u8() -> bool {
    let b: Box<u8> = Box::new(42);
    *b == 42
}

#[rust_lean_test]
pub fn test_box_new_deref_bool_true() -> bool {
    let b: Box<bool> = Box::new(true);
    *b == true
}

#[rust_lean_test]
pub fn test_box_new_deref_bool_false() -> bool {
    let b: Box<bool> = Box::new(false);
    *b == false
}

// ----- Box::new wider integer ------------------------------------------------

#[rust_lean_test]
pub fn test_box_new_deref_u32_zero() -> bool {
    let b: Box<u32> = Box::new(0);
    *b == 0
}

#[rust_lean_test]
pub fn test_box_new_deref_u32_max() -> bool {
    let b: Box<u32> = Box::new(u32::MAX);
    *b == u32::MAX
}

#[rust_lean_test]
pub fn test_box_new_deref_i32_neg() -> bool {
    let b: Box<i32> = Box::new(-7);
    *b == -7
}

// ----- Double deref via reborrow --------------------------------------------

#[rust_lean_test]
pub fn test_box_double_deref_zero() -> bool {
    let b: Box<u8> = Box::new(0);
    let r: &Box<u8> = &b;
    **r == 0
}

#[rust_lean_test]
pub fn test_box_double_deref_max() -> bool {
    let b: Box<u8> = Box::new(u8::MAX);
    let r: &Box<u8> = &b;
    **r == u8::MAX
}

#[rust_lean_test]
pub fn test_box_double_deref_mid() -> bool {
    let b: Box<u8> = Box::new(123);
    let r: &Box<u8> = &b;
    **r == 123
}

// ----- Mutation through Box -------------------------------------------------

#[rust_lean_test]
pub fn test_box_mut_assign() -> bool {
    let mut b: Box<u8> = Box::new(1);
    *b = 9;
    *b == 9
}

#[rust_lean_test]
pub fn test_box_mut_increment() -> bool {
    let mut b: Box<u8> = Box::new(10);
    *b = *b + 5;
    *b == 15
}

// ----- Box::into_inner ------------------------------------------------------

#[rust_lean_test]
pub fn test_box_into_inner_zero() -> bool {
    Box::into_inner(Box::new(0u8)) == 0
}

#[rust_lean_test]
pub fn test_box_into_inner_max_u8() -> bool {
    Box::into_inner(Box::new(u8::MAX)) == u8::MAX
}

#[rust_lean_test]
pub fn test_box_into_inner_min_i8() -> bool {
    Box::into_inner(Box::new(i8::MIN)) == i8::MIN
}

#[rust_lean_test]
pub fn test_box_into_inner_bool() -> bool {
    Box::into_inner(Box::new(true))
}

#[rust_lean_test]
pub fn test_box_into_inner_tuple() -> bool {
    let (a, b) = Box::into_inner(Box::new((7u8, 9u8)));
    a == 7 && b == 9
}

// `into_inner` must move the value out rather than reconstruct it: with
// `Bumped`, a `clone` on the way out would be observable (`clone` bumps by 1
// and `eq` compares the bumped values, so `Bumped(3) == Bumped(4)` is false).
#[rust_lean_test]
pub fn test_box_into_inner_bumped_not_cloned() -> bool {
    Box::into_inner(Box::new(Bumped(3))) == Bumped(3)
}

// ----- Box::into_boxed_slice -------------------------------------------------

#[rust_lean_test]
pub fn test_box_into_boxed_slice_len() -> bool {
    Box::into_boxed_slice(Box::new(5u8)).len() == 1
}

#[rust_lean_test]
pub fn test_box_into_boxed_slice_element() -> bool {
    Box::into_boxed_slice(Box::new(5u8))[0] == 5
}

#[rust_lean_test]
pub fn test_box_into_boxed_slice_max_u8() -> bool {
    Box::into_boxed_slice(Box::new(u8::MAX))[0] == u8::MAX
}

#[rust_lean_test]
pub fn test_box_into_boxed_slice_min_i8() -> bool {
    Box::into_boxed_slice(Box::new(i8::MIN))[0] == i8::MIN
}

#[rust_lean_test]
pub fn test_box_into_boxed_slice_not_empty() -> bool {
    !Box::into_boxed_slice(Box::new(0u8)).is_empty()
}

// ----- Box::map -------------------------------------------------------------

#[rust_lean_test]
pub fn test_box_map_add() -> bool {
    *Box::map(Box::new(7u8), |x| x + 7) == 14
}

#[rust_lean_test]
pub fn test_box_map_zero() -> bool {
    *Box::map(Box::new(0u8), |x| x + 1) == 1
}

#[rust_lean_test]
pub fn test_box_map_widens_type() -> bool {
    *Box::map(Box::new(u8::MAX), |x| x as u32 + 1) == 256
}

#[rust_lean_test]
pub fn test_box_map_to_bool() -> bool {
    *Box::map(Box::new(0u8), |x| x == 0)
}

#[rust_lean_test]
pub fn test_box_map_min_i8() -> bool {
    *Box::map(Box::new(i8::MIN), |x| x + 1) == -127
}

// ----- Box::new_in ----------------------------------------------------------

#[rust_lean_test]
pub fn test_box_new_in_zero() -> bool {
    *Box::new_in(0u8, Global) == 0
}

#[rust_lean_test]
pub fn test_box_new_in_max_u8() -> bool {
    *Box::new_in(u8::MAX, Global) == u8::MAX
}

#[rust_lean_test]
pub fn test_box_new_in_min_i8() -> bool {
    *Box::new_in(i8::MIN, Global) == i8::MIN
}

#[rust_lean_test]
pub fn test_box_new_in_bool() -> bool {
    *Box::new_in(true, Global)
}

#[rust_lean_test]
pub fn test_box_new_in_matches_new() -> bool {
    *Box::new_in(42u8, Global) == *Box::new(42u8)
}
