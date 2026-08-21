//! Equivalence tests for `core::marker::*`.
//!
//! Almost everything in `core::marker` is an *empty* marker trait — `Freeze`,
//! `Unpin`, `MetaSized`, `PointeeSized`, `Destruct`, `Tuple`, `Unsize`,
//! `ConstParamTy_`, `DiscriminantKind`, `FnPtr` — whose implementors the
//! compiler chooses and which have no methods, hence no observation for a point
//! test to pin. The model declares them without blanket impls, so a test that
//! merely *bounded* a type parameter by one would fail to find an instance in
//! the extraction rather than check anything.
//!
//! That leaves the zero-sized marker *types*, which do reach a value level:
//! `PhantomData` and `PhantomPinned` below.
//!
//! The `Phantom{Co,Contra,In}variant{,Lifetime}` markers and `variance()` are
//! unstable in std (`feature(phantom_variance_markers)`), so — like
//! `core::hint::must_use` — there is no call path to them from this crate. They
//! are exercised from the model crate's own `#[cfg(test)]` block instead.

use rust_lean_test_macro::rust_lean_test;

// ----- PhantomData -----------------------------------------------------------

pub struct Tagged<T>(pub u8, pub core::marker::PhantomData<T>);

#[rust_lean_test]
pub fn test_phantom_data_keeps_payload() -> bool {
    let t: Tagged<u32> = Tagged(7, core::marker::PhantomData);
    t.0 == 7
}

#[rust_lean_test]
pub fn test_phantom_data_payload_zero() -> bool {
    let t: Tagged<u32> = Tagged(0, core::marker::PhantomData);
    t.0 == 0
}

#[rust_lean_test]
pub fn test_phantom_data_payload_max() -> bool {
    let t: Tagged<u8> = Tagged(u8::MAX, core::marker::PhantomData);
    t.0 == u8::MAX
}

// ----- PhantomPinned ---------------------------------------------------------

pub struct Pinned(pub u8, pub core::marker::PhantomPinned);

#[rust_lean_test]
pub fn test_phantom_pinned_keeps_payload() -> bool {
    let p = Pinned(7, core::marker::PhantomPinned);
    p.0 == 7
}

#[rust_lean_test]
pub fn test_phantom_pinned_payload_zero() -> bool {
    let p = Pinned(0, core::marker::PhantomPinned);
    p.0 == 0
}

#[rust_lean_test]
pub fn test_phantom_pinned_payload_max() -> bool {
    let p = Pinned(u8::MAX, core::marker::PhantomPinned);
    p.0 == u8::MAX
}

// ----- variance / Phantom*Variance* (unstable in std, no call path) -----------
//
// #[rust_lean_test]
// pub fn test_variance_is_default() -> bool {
//     let v: core::marker::PhantomCovariant<u8> = core::marker::variance();
//     v == core::marker::PhantomCovariant::new()
// }
//
// TODO(phantom-variance-markers-stability): turn this on once
// `feature(phantom_variance_markers)` is stable, or this crate starts opting
// into nightly features.
