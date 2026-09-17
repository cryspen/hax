//! Model of `core::alloc` — the `Layout` type only.
//!
//! `core::alloc::global::GlobalAlloc` is out of scope: its methods are typed
//! with raw pointers, which the model does not have.
//!
//! Lean-only: F* drops this module via the Makefile's `-i` flags.

/// See [`std::alloc::Layout`]
pub mod layout {
    /// See [`std::alloc::Layout`]
    pub struct Layout {
        size: core::primitive::usize,
        align: crate::ptr::alignment::Alignment,
    }

    /// See [`std::alloc::LayoutError`]
    pub struct LayoutError;

    /// See [`std::fmt::Debug`] for [`LayoutError`]
    #[cfg(not(hax_backend_fstar))]
    impl crate::fmt::Debug for LayoutError {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }

    #[cfg(all(test, not(hax_backend_fstar)))]
    mod tests {
        /// `Debug` for `LayoutError` renders nothing, like every other `Debug`
        /// in the model.
        #[test]
        fn test_layout_error_debug() {
            let mut f = crate::fmt::Formatter;
            assert!(crate::fmt::Debug::fmt(&super::LayoutError, &mut f).is_ok());
        }
    }
}
