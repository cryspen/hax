//! Model of `core::alloc` — the `Layout` type only.
//!
//! `core::alloc::global::GlobalAlloc` is out of scope: its methods are typed
//! with raw pointers, which the model does not have.
//!
//! Lean-only: F* drops this module via the Makefile's `-i` flags.

/// See [`std::alloc::Layout`]
pub mod layout {
    /// See [`std::alloc::Layout`]
    ///
    /// The two fields real `core` has, and the two Aeneas's Lean library models.
    /// No operations: every constructor in real `core` checks alignment
    /// invariants the model has no way to state.
    pub struct Layout {
        size: core::primitive::usize,
        align: crate::ptr::alignment::Alignment,
    }

    /// See [`std::alloc::LayoutError`]
    pub struct LayoutError;
}
