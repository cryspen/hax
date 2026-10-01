//! Equivalence tests for `core::marker::*`. Only the marker types are tested:
//! the marker traits have no methods to observe.

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
