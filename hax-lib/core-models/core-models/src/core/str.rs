mod converts {
    #[hax_lib::opaque]
    #[cfg_attr(charon, charon::opaque)]
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
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err> {
            let (parsed, value) = rust_primitives::string::str_parse_u64(s);
            if parsed {
                crate::result::Result::Ok(value)
            } else {
                // DEVIATION(std): the error type is `u64` here, not
                // `ParseIntError`, so there is no payload to report.
                crate::result::Result::Err(0)
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::FromStr;
        use crate::result::Result;
        use proptest::prelude::*;

        proptest! {
            // Both a digit-shaped and a free-form generator, so the `Ok` and the
            // `Err` side are each reached.
            #[test]
            fn test_u64_from_str(s in prop_oneof!["[0-9]{0,25}", ".*"]) {
                let std_result = s.parse::<u64>();
                match <u64 as FromStr>::from_str(&s) {
                    Result::Ok(v) => prop_assert_eq!(Ok(v), std_result),
                    Result::Err(_) => prop_assert!(std_result.is_err()),
                }
            }
        }
    }
}
