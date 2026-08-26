//! Equivalence tests for `core::error::*`.
//!
//! Nothing here has a Lean half. `Error::description` is a trait *default*
//! method in core, and the model provides it through the blanket-implemented
//! `error::ErrorDefaults` companion trait — Aeneas resolves the call to
//! `core_models::error::Error::description`, which does not exist, so a
//! `#[rust_lean_test]` here would break the Lean build with an unknown
//! constant. The blanket impl is `hax_lib::exclude`d on top of that, because
//! Aeneas cannot translate a body returning a `&'static str`.

#[cfg(test)]
mod description {
    use core::error::Error;
    use core::fmt;

    #[derive(Debug)]
    struct E;

    impl fmt::Display for E {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("e")
        }
    }

    impl Error for E {}

    #[test]
    fn test_description_default() {
        #[allow(deprecated)]
        let description = E.description();
        assert_eq!(description, "description() is deprecated; use Display");
    }
}
