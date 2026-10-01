//! Model of `core::sync::atomic` — the two atomic types Aeneas declares.
//!
//! No interior mutability or concurrency here, so each is a plain newtype with
//! no operations. Lean-only: F* drops this module via the Makefile's `-i` flags.
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
