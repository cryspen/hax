mod converts {
    #[hax_lib::opaque]
    fn from_utf8(s: &[u8]) -> crate::result::Result<&str, super::error::Utf8Error> {
        let (valid, decoded) = rust_primitives::string::str_from_utf8(s);
        if valid {
            crate::result::Result::Ok(decoded)
        } else {
            crate::result::Result::Err(super::error::Utf8Error)
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::testing::Inject;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_from_utf8(bytes in prop::collection::vec(any::<u8>(), 0..20)) {
                prop_assert_eq!(
                    super::from_utf8(&bytes),
                    std::str::from_utf8(&bytes).inject()
                );
            }

            // Random bytes are rarely valid UTF-8; go through a real `String` to
            // exercise the `Ok` side as well.
            #[test]
            fn test_from_utf8_valid(text in ".*") {
                let bytes = text.as_bytes();
                prop_assert_eq!(super::from_utf8(bytes), std::str::from_utf8(bytes).inject());
            }
        }
    }
}

mod error {
    /// See [`std::str::Utf8Error`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct Utf8Error;

    /// The model's error carries no position, so every std one maps here.
    #[cfg(test)]
    impl crate::testing::Inject for std::str::Utf8Error {
        type Model = Utf8Error;
        fn inject(&self) -> Self::Model {
            Utf8Error
        }
    }
}

mod iter {
    struct Split<T>(T);
}

mod traits {
    trait FromStr: Sized {
        type Err;
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err>;
    }

    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    impl FromStr for u64 {
        type Err = u64;
        // Excluded from coverage: the Lean library models no string
        // primitives, so an implemented body cannot be extracted; it stays a
        // placeholder.
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err> {
            panic!()
        }
    }
}
