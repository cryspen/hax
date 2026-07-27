//! Equivalence tests for `alloc::boxed::Box::*`.
//!
//! The model in `alloc/src/lib.rs` makes `Box::new(v)` the identity (hax
//! erases boxes), so on the Lean side `Box<T>` is `T`. The Rust side still
//! constructs a real `Box`, so dereferencing `*b` and reborrowing `&**b`
//! both have to agree with the model.
//!
//! There are no proptest cases for `Box` in `alloc/src/lib.rs`; the cases
//! below are hand-picked to cover construction, single-deref, and
//! double-deref via a reborrow.

use rust_lean_test_macro::rust_lean_test;

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
