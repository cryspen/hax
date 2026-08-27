// F*-only: `charon::opaque` drops the declaration too, and extracted bodies
// across the model call these, so Lean would not elaborate.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic_explicit() -> ! {
    panic!()
}

#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic(_msg: &str) -> ! {
    panic!()
}

#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic_fmt(_fmt: super::fmt::Arguments) -> ! {
    panic!()
}

/// `core::panicking::AssertKind` — which of `assert_eq!` / `assert_ne!` /
/// `assert_matches!` failed. Carried by the `assert_failed` shims; the model
/// has no use for it beyond giving a client's mention of it a name.
pub enum AssertKind {
    /// `core::panicking::AssertKind::Eq`
    Eq,
    /// `core::panicking::AssertKind::Ne`
    Ne,
    /// `core::panicking::AssertKind::Match`
    Match,
}

pub mod internal {
    // This module is used to break a dependency cycle (other core modules have
    // panics and this brings a dependency on core::fmt that we need to avoid)
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(false)]
    pub fn panic<T>() -> T {
        panic!("")
    }
}

// These all return `!`, so `should_panic` is the only way to run them. There is
// no public `core` counterpart to compare against (`core::panicking` is
// internal), hence no `panics_like_core` here. `panic_fmt` is tested from
// `fmt`'s test module, the only place an `Arguments` can be built.
#[cfg(test)]
mod tests {
    #[test]
    #[should_panic]
    fn test_panic_explicit() {
        super::panic_explicit()
    }

    #[test]
    #[should_panic]
    fn test_panic() {
        super::panic("boom")
    }

    #[test]
    #[should_panic]
    fn test_internal_panic() {
        super::internal::panic::<()>()
    }
}
