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
        use crate::result::Result;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_from_utf8(bytes in prop::collection::vec(any::<u8>(), 0..20)) {
                let std_result = std::str::from_utf8(&bytes);
                match super::from_utf8(&bytes) {
                    Result::Ok(s) => prop_assert_eq!(Ok(s), std_result),
                    Result::Err(_) => prop_assert!(std_result.is_err()),
                }
            }

            // Random bytes are rarely valid UTF-8; go through a real `String` to
            // exercise the `Ok` side as well.
            #[test]
            fn test_from_utf8_valid(text in ".*") {
                let bytes = text.as_bytes();
                match super::from_utf8(bytes) {
                    Result::Ok(s) => prop_assert_eq!(s, text.as_str()),
                    Result::Err(_) => prop_assert!(false, "valid UTF-8 rejected"),
                }
            }
        }
    }
}

mod error {
    /// See [`std::str::Utf8Error`]
    pub struct Utf8Error;
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
