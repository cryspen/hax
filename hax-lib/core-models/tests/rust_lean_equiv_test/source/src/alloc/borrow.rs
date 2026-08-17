//! Equivalence tests for `alloc::borrow::*`.
//!
//! Mirrors the proptest cases in `alloc/src/lib.rs` (module `borrow::tests`).
//!
//! Only `u8` is exercised: the model's blanket `ToOwned` has `Owned = Self`,
//! which agrees with real `alloc` for `u8` (`<u8 as ToOwned>::Owned == u8`) but
//! not for unsized types like `[T]` / `str`, whose `Owned` is `Vec<T>` /
//! `String`.

use crate::helpers::Bumped;
use rust_lean_test_macro::rust_lean_test;
use std::borrow::Cow;

// ----- ToOwned::to_owned -----------------------------------------------------

#[rust_lean_test]
pub fn test_to_owned_zero() -> bool {
    let x: u8 = 0;
    x.to_owned() == 0
}

#[rust_lean_test]
pub fn test_to_owned_max() -> bool {
    let x: u8 = u8::MAX;
    x.to_owned() == u8::MAX
}

#[rust_lean_test]
pub fn test_to_owned_bool() -> bool {
    let x: bool = true;
    x.to_owned() == true
}

// `to_owned` goes through `T: Clone`, so the appended value is
// `Bumped(1).clone()`.
#[rust_lean_test]
pub fn test_to_owned_applies_clone() -> bool {
    let x = Bumped(1);
    x.to_owned().0 == 2
}

// ----- ToOwned::clone_into ---------------------------------------------------

// TODO(trait-default-method): `clone_into` is a trait *default* method in real
// `alloc`, which hax cannot express; the model provides it on the companion
// trait `ToOwnedDefaults`, so a client's `x.clone_into(&mut t)` resolves to
// `ToOwned::clone_into`, which the model does not define. Same situation as
// `PartialEq::ne` vs `core_models::cmp::Neq::neq`. Covered by the property test
// in `alloc/src/lib.rs`.

// ----- Cow::is_borrowed / Cow::is_owned --------------------------------------

#[rust_lean_test]
pub fn test_cow_borrowed_is_borrowed() -> bool {
    let c: Cow<u8> = Cow::Borrowed(&7);
    Cow::is_borrowed(&c) == true
}

#[rust_lean_test]
pub fn test_cow_borrowed_is_owned() -> bool {
    let c: Cow<u8> = Cow::Borrowed(&7);
    Cow::is_owned(&c) == false
}

#[rust_lean_test]
pub fn test_cow_owned_is_borrowed() -> bool {
    let c: Cow<u8> = Cow::Owned(7);
    Cow::is_borrowed(&c) == false
}

#[rust_lean_test]
pub fn test_cow_owned_is_owned() -> bool {
    let c: Cow<u8> = Cow::Owned(7);
    Cow::is_owned(&c) == true
}

// ----- Cow::into_owned -------------------------------------------------------

#[rust_lean_test]
pub fn test_cow_into_owned_borrowed() -> bool {
    let c: Cow<u8> = Cow::Borrowed(&9);
    c.into_owned() == 9
}

#[rust_lean_test]
pub fn test_cow_into_owned_owned() -> bool {
    let c: Cow<u8> = Cow::Owned(u8::MAX);
    c.into_owned() == u8::MAX
}

#[rust_lean_test]
pub fn test_cow_into_owned_zero() -> bool {
    let c: Cow<u8> = Cow::Borrowed(&0);
    c.into_owned() == 0
}

// ----- Cow::to_mut -----------------------------------------------------------

// TODO(mut-return): real `Cow::to_mut` returns `&mut B::Owned`, so a client's
// call site expects the value *and* a write-back function. The model returns the
// owned value instead (see its `DEVIATION` note), which is one component short.
// Covered by the property test in `alloc/src/lib.rs`.
