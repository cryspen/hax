use super::fmt::{Debug, Display};

/// See [`std::error::Error`]
pub trait Error: Display + Debug {}

// `Error::description` is a trait default method in core, which hax does not
// support, so it goes through a blanket-implemented companion trait like
// `cmp::Neq` and `iter::IteratorMethods` do.
trait ErrorDefaults {
    /// See [`std::error::Error::description`]
    fn description(&self) -> &str;
}

// Hidden from Aeneas: it cannot translate a body that returns a `&'static str`
// ("There should be no bottoms in the value") and would emit a `sorry`. The F*
// extraction of this module is interface-only, so it keeps only the signature.
#[cfg_attr(charon, aeneas::exclude)]
impl<T: Error> ErrorDefaults for T {
    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, ErrorDefaults};
    use crate::fmt::{Display, Formatter, Result};

    struct ModelError;

    impl Display for ModelError {
        fn fmt(&self, f: &mut Formatter) -> Result {
            Result::Ok(())
        }
    }

    impl Error for ModelError {}

    #[derive(Debug)]
    struct StdError;

    impl core::fmt::Display for StdError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("std error")
        }
    }

    impl core::error::Error for StdError {}

    // The two `Display` impls are here to satisfy `Error`'s supertrait bound,
    // and `description` never calls them; this runs both so the pair is
    // exercised rather than merely declared. The model's `fmt` writes nothing
    // and cannot fail, so running it is the whole check — matching on its
    // `Result` would leave the `Err` arm unreachable — and the std side is what
    // carries an assertion.
    #[test]
    fn test_display_impls_run() {
        let mut f = Formatter;
        let _: Result = Display::fmt(&ModelError, &mut f);
        assert_eq!(std::format!("{}", StdError), "std error");
    }

    // `description` takes no input, so this is a single comparison against the
    // default body in real core rather than a proptest.
    #[test]
    fn test_description_matches_core() {
        #[allow(deprecated)]
        let expected = core::error::Error::description(&StdError);
        assert_eq!(ErrorDefaults::description(&ModelError), expected);
    }
}
