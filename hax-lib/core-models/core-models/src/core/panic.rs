//! Model of `core::panic` — the payload types a panic hook is handed.
//!
//! Every model panic diverges, so nothing here is ever constructed; the types
//! exist so a client mentioning them has a name to resolve to, which is all
//! Aeneas gives them too.
//!
//! Lean-only: F* drops this module via the Makefile's `-i` flags.
/// See [`std::panic::Location`]
pub mod location {
    /// See [`std::panic::Location`]
    ///
    /// Real `core` stores the filename as a `NonNull<str>` plus a `PhantomData`
    /// so that it can keep a NUL terminator past the end; the model has no raw
    /// pointers, so it holds the `&str` directly.
    pub struct Location<'a> {
        filename: &'a str,
        line: core::primitive::u32,
        col: core::primitive::u32,
    }
}

/// See [`std::panic::PanicInfo`]
pub mod panic_info {
    /// See [`std::panic::PanicInfo`]
    pub struct PanicInfo<'a> {
        message: &'a crate::fmt::Arguments<'a>,
        location: &'a super::location::Location<'a>,
        can_unwind: core::primitive::bool,
        force_no_backtrace: core::primitive::bool,
    }
}
