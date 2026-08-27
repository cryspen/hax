//! Model of `core::pin`.
//!
//! Pinning is a compile-time discipline with no runtime content, so both types
//! below are the `repr(transparent)` newtypes real `core` has and nothing else
//! — which is what Aeneas's Lean library declares them as (an axiom apiece).
//!
//! Lean-only: the F* extraction drops this module through the `-i` flags on the
//! `fstar-core-models` target in the Makefile.

/// See [`std::pin::Pin`]
pub struct Pin<Ptr> {
    pointer: Ptr,
}

/// `core::pin::helper` — the `repr(transparent)` twin of [`Pin`] that
/// `Pin::as_mut` casts through (rust-lang/rust#85099).
pub mod helper {
    /// `core::pin::helper::PinHelper`
    pub struct PinHelper<Ptr> {
        pointer: Ptr,
    }
}
