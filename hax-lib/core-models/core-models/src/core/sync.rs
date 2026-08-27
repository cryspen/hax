//! Model of `core::sync::atomic` — the two atomic types Aeneas's Lean library
//! declares.
//!
//! Real `core` wraps an `UnsafeCell`; the model has neither interior mutability
//! nor concurrency, so each one is a plain newtype over its value and carries no
//! operations (Aeneas declares them as axioms).
//!
//! Lean-only: the F* extraction drops this module through the `-i` flags on the
//! `fstar-core-models` target in the Makefile.

/// See [`std::sync::atomic`]
pub mod atomic {
    /// See [`std::sync::atomic::AtomicBool`]
    ///
    /// Real `core` holds an `UnsafeCell<u8>`, hence the `u8` rather than a
    /// `bool`.
    pub struct AtomicBool {
        v: core::primitive::u8,
    }

    /// See [`std::sync::atomic::AtomicU32`]
    pub struct AtomicU32 {
        v: core::primitive::u32,
    }
}
