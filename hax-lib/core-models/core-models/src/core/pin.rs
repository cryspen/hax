//! Model of `core::pin`. Pinning has no runtime content, so both types are the
//! `repr(transparent)` newtypes real `core` has and nothing else.
//!
//! Lean-only: F* drops this module via the Makefile's `-i` flags.
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
