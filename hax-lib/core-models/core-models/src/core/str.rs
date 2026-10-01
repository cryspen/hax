//! Model of the byte-oriented part of `core::str`. `Pattern` methods are left out: aeneas
//! cannot translate `core`'s `Pattern`, which would abort extracting any caller.
#![allow(non_camel_case_types)]

use crate::option::Option;
use rust_primitives::slice::{slice_index, slice_length};
use rust_primitives::string::{str_as_bytes, str_sub_bytes};

/// See [`std::primitive::str`]
/// Stand-in for the primitive, which cannot have inherent impls (like `slice::Slice`).
// F*-only: `charon::exclude` would drop it while its impls still refer to it.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct str;

/// Same set as `u8::is_ascii_whitespace`, which excludes vertical tab.
fn is_ascii_whitespace_byte(b: core::primitive::u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D
}

fn ascii_lowercase_byte(b: core::primitive::u8) -> core::primitive::u8 {
    if b >= 0x41 && b <= 0x5A { b + 0x20 } else { b }
}

#[hax_lib::attributes]
impl str {
    /// See [`std::primitive::str::as_bytes`]
    fn as_bytes(s: &core::primitive::str) -> &[core::primitive::u8] {
        str_as_bytes(s)
    }
    /// See [`std::primitive::str::len`]
    fn len(s: &core::primitive::str) -> usize {
        slice_length(str_as_bytes(s))
    }
    /// See [`std::primitive::str::is_empty`]
    fn is_empty(s: &core::primitive::str) -> bool {
        Self::len(s) == 0
    }
    /// See [`std::primitive::str::as_str`]
    fn as_str(s: &core::primitive::str) -> &core::primitive::str {
        s
    }
    /// See [`std::primitive::str::is_char_boundary`]
    fn is_char_boundary(s: &core::primitive::str, index: usize) -> bool {
        let bytes = Self::as_bytes(s);
        let n = slice_length(bytes);
        if index == 0 {
            true
        } else if index >= n {
            index == n
        } else {
            (*slice_index(bytes, index) & 0xC0) != 0x80
        }
    }
    /// See [`std::primitive::str::floor_char_boundary`]
    fn floor_char_boundary(s: &core::primitive::str, index: usize) -> usize {
        let n = Self::len(s);
        if index >= n {
            n
        } else {
            // Forward scan: a decreasing loop extracts worse.
            let mut res = 0;
            for i in 0..index + 1 {
                if Self::is_char_boundary(s, i) {
                    res = i;
                }
            }
            res
        }
    }
    /// See [`std::primitive::str::ceil_char_boundary`]
    #[hax_lib::requires(index <= str::len(s))]
    fn ceil_char_boundary(s: &core::primitive::str, index: usize) -> usize {
        let n = Self::len(s);
        if index > n {
            crate::panicking::internal::panic()
        } else if index == n {
            n
        } else {
            let mut res = n;
            let mut found = false;
            for i in index..n {
                if !found && Self::is_char_boundary(s, i) {
                    res = i;
                    found = true;
                }
            }
            res
        }
    }
    /// See [`std::primitive::str::split_at`]
    #[hax_lib::requires(str::is_char_boundary(s, mid))]
    fn split_at(
        s: &core::primitive::str,
        mid: usize,
    ) -> (&core::primitive::str, &core::primitive::str) {
        if !Self::is_char_boundary(s, mid) {
            crate::panicking::internal::panic()
        }
        (
            str_sub_bytes(s, 0, mid),
            str_sub_bytes(s, mid, Self::len(s)),
        )
    }
    /// See [`std::primitive::str::split_at_checked`]
    fn split_at_checked(
        s: &core::primitive::str,
        mid: usize,
    ) -> Option<(&core::primitive::str, &core::primitive::str)> {
        if Self::is_char_boundary(s, mid) {
            Option::Some(Self::split_at(s, mid))
        } else {
            Option::None
        }
    }
    /// See [`std::primitive::str::is_ascii`]
    fn is_ascii(s: &core::primitive::str) -> bool {
        let bytes = Self::as_bytes(s);
        let mut res = true;
        for i in 0..slice_length(bytes) {
            if *slice_index(bytes, i) > 0x7F {
                res = false;
            }
        }
        res
    }
    /// See [`std::primitive::str::eq_ignore_ascii_case`]
    fn eq_ignore_ascii_case(s: &core::primitive::str, other: &core::primitive::str) -> bool {
        let a = Self::as_bytes(s);
        let b = Self::as_bytes(other);
        if slice_length(a) != slice_length(b) {
            false
        } else {
            let mut res = true;
            for i in 0..slice_length(a) {
                if ascii_lowercase_byte(*slice_index(a, i))
                    != ascii_lowercase_byte(*slice_index(b, i))
                {
                    res = false;
                }
            }
            res
        }
    }
    /// See [`std::primitive::str::trim_ascii_start`]
    fn trim_ascii_start(s: &core::primitive::str) -> &core::primitive::str {
        let bytes = Self::as_bytes(s);
        let n = slice_length(bytes);
        let mut start = n;
        let mut found = false;
        for i in 0..n {
            if !found && !is_ascii_whitespace_byte(*slice_index(bytes, i)) {
                start = i;
                found = true;
            }
        }
        str_sub_bytes(s, start, n)
    }
    /// See [`std::primitive::str::trim_ascii_end`]
    // Not `end`: aeneas escapes that Lean keyword into colliding names.
    fn trim_ascii_end(s: &core::primitive::str) -> &core::primitive::str {
        let bytes = Self::as_bytes(s);
        let n = slice_length(bytes);
        let mut last = 0;
        for i in 0..n {
            if !is_ascii_whitespace_byte(*slice_index(bytes, i)) {
                last = i + 1;
            }
        }
        str_sub_bytes(s, 0, last)
    }
    /// See [`std::primitive::str::trim_ascii`]
    fn trim_ascii(s: &core::primitive::str) -> &core::primitive::str {
        Self::trim_ascii_end(Self::trim_ascii_start(s))
    }
    /// See [`std::primitive::str::parse`]
    fn parse<F: traits::FromStr>(s: &core::primitive::str) -> crate::result::Result<F, F::Err> {
        F::from_str(s)
    }
}

/// `PartialEq for str`, in a submodule so that `str::traits` avoids an F* module cycle.
pub mod equality {
    use super::str;
    use rust_primitives::slice::{slice_index, slice_length};

    // Byte loop, not `[u8]`'s `eq`: aeneas cannot resolve that instance from here.
    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl crate::cmp::PartialEq<core::primitive::str> for core::primitive::str {
        fn eq(&self, other: &core::primitive::str) -> bool {
            let a = str::as_bytes(self);
            let b = str::as_bytes(other);
            if slice_length(a) != slice_length(b) {
                false
            } else {
                let mut res = true;
                for i in 0..slice_length(a) {
                    if *slice_index(a, i) != *slice_index(b, i) {
                        res = false;
                    }
                }
                res
            }
        }
    }
}

mod converts {
    // Opaque: the model cannot decide UTF-8 validity.
    #[hax_lib::opaque]
    fn from_utf8(s: &[u8]) -> crate::result::Result<&str, super::error::Utf8Error> {
        let (valid, decoded, valid_up_to, error_len) = rust_primitives::string::str_from_utf8(s);
        if valid {
            crate::result::Result::Ok(decoded)
        } else {
            crate::result::Result::Err(super::error::Utf8Error::new(valid_up_to, error_len))
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

pub mod error {
    use crate::option::Option;

    /// See [`std::str::Utf8Error`]. Fields are `pub(super)` (private in core) for tests.
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct Utf8Error {
        pub(super) valid_up_to: usize,
        pub(super) error_len: Option<u8>,
    }

    /// See [`std::fmt::Debug`] for [`Utf8Error`]
    #[cfg(not(hax_backend_fstar))]
    impl crate::fmt::Debug for Utf8Error {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }

    // The unused lifetime makes hax name the methods `impl__*`, as for core's, rather
    // than `impl_Utf8Error__*`.
    impl<'a> Utf8Error {
        /// `error_len == 0` encodes `None`.
        pub(super) fn new(valid_up_to: usize, error_len: u8) -> Utf8Error {
            Utf8Error {
                valid_up_to,
                error_len: if error_len == 0 {
                    Option::None
                } else {
                    Option::Some(error_len)
                },
            }
        }

        /// See [`std::str::Utf8Error::valid_up_to`]
        pub fn valid_up_to(&self) -> usize {
            self.valid_up_to
        }
        /// See [`std::str::Utf8Error::error_len`]
        pub fn error_len(&self) -> Option<usize> {
            match self.error_len {
                Option::Some(len) => Option::Some(len as usize),
                Option::None => Option::None,
            }
        }
    }

    #[cfg(test)]
    impl crate::testing::Inject for std::str::Utf8Error {
        type Model = Utf8Error;
        fn inject(&self) -> Self::Model {
            Utf8Error {
                valid_up_to: self.valid_up_to(),
                error_len: match self.error_len() {
                    ::core::option::Option::Some(len) => Option::Some(len as u8),
                    ::core::option::Option::None => Option::None,
                },
            }
        }
    }

    /// See [`std::str::ParseBoolError`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct ParseBoolError;

    // Excluded from F*, where equality on this unit struct is structural.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    impl crate::cmp::PartialEq<ParseBoolError> for ParseBoolError {
        fn eq(&self, _other: &Self) -> bool {
            true
        }
    }

    #[cfg(all(test, not(hax_backend_fstar)))]
    mod tests {
        /// `Debug` for `Utf8Error` renders nothing, like every other `Debug` in
        /// the model.
        #[test]
        fn test_utf8_error_debug() {
            let mut f = crate::fmt::Formatter;
            assert!(crate::fmt::Debug::fmt(&super::Utf8Error::new(0, 0), &mut f).is_ok());
        }
    }
}

mod iter {
    struct Split<T>(T);
}

pub mod traits {
    pub trait FromStr: Sized {
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

    // Opaque in F*: it cannot resolve `PartialEq for str` here, hax mangles the literals
    // to `r#true`, and the body would add a module cycle via `str`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl FromStr for bool {
        type Err = super::error::ParseBoolError;
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err> {
            if crate::cmp::PartialEq::eq(s, "true") {
                crate::result::Result::Ok(true)
            } else if crate::cmp::PartialEq::eq(s, "false") {
                crate::result::Result::Ok(false)
            } else {
                crate::result::Result::Err(super::error::ParseBoolError)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::error::{ParseBoolError, Utf8Error};
    use super::str;
    use crate::option::Option as ModelOption;
    use crate::result::Result as ModelResult;
    use crate::testing::Inject;
    use proptest::prelude::*;

    fn any_str() -> impl Strategy<Value = String> {
        prop::collection::vec(any::<char>(), 0..=8).prop_map(|cs| cs.into_iter().collect())
    }

    /// Includes vertical tab, which is not ASCII whitespace.
    fn ws_str() -> impl Strategy<Value = String> {
        prop::collection::vec(
            prop::sample::select(vec![
                ' ', '\t', '\n', '\r', '\u{0c}', '\u{0b}', 'a', 'Z', 'é',
            ]),
            0..=8,
        )
        .prop_map(|cs| cs.into_iter().collect())
    }

    /// Pairs often equal up to ASCII case.
    fn case_pair() -> impl Strategy<Value = (String, String)> {
        prop::collection::vec(
            (
                prop::sample::select(vec!['a', 'B', 'c', 'D', 'é']),
                any::<bool>(),
            ),
            0..=6,
        )
        .prop_map(|v| {
            let a: String = v.iter().map(|p| p.0).collect();
            let b: String = v
                .iter()
                .map(|p| {
                    if p.1 {
                        p.0.to_ascii_uppercase()
                    } else {
                        p.0.to_ascii_lowercase()
                    }
                })
                .collect();
            (a, b)
        })
    }

    /// Spec of `floor_char_boundary`, whose std version is unstable.
    fn floor_oracle(s: &core::primitive::str, index: usize) -> usize {
        (0..=index.min(s.len()))
            .rev()
            .find(|i| s.is_char_boundary(*i))
            .unwrap()
    }

    /// Spec of `ceil_char_boundary`, for `index <= s.len()`.
    fn ceil_oracle(s: &core::primitive::str, index: usize) -> usize {
        (index..=s.len()).find(|i| s.is_char_boundary(*i)).unwrap()
    }

    proptest! {
        #[test]
        fn test_len(s in any_str()) {
            prop_assert_eq!(str::len(&s), s.len());
        }

        #[test]
        fn test_is_empty(s in any_str()) {
            prop_assert_eq!(str::is_empty(&s), s.is_empty());
        }

        #[test]
        fn test_as_bytes(s in any_str()) {
            prop_assert_eq!(str::as_bytes(&s), s.as_bytes());
        }

        #[test]
        fn test_as_str(s in any_str()) {
            prop_assert_eq!(str::as_str(&s), s.as_str());
        }

        #[test]
        fn test_is_char_boundary(s in any_str(), index in 0usize..=32) {
            prop_assert_eq!(str::is_char_boundary(&s, index), s.is_char_boundary(index));
        }

        #[test]
        fn test_floor_char_boundary(s in any_str(), index in 0usize..=32) {
            prop_assert_eq!(str::floor_char_boundary(&s, index), floor_oracle(&s, index));
        }

        #[test]
        fn test_ceil_char_boundary(s in any_str(), index in 0usize..=32) {
            prop_assume!(index <= s.len());
            prop_assert_eq!(str::ceil_char_boundary(&s, index), ceil_oracle(&s, index));
        }

        #[test]
        // Snap `mid` to a boundary: random indices rarely land on one.
        fn test_split_at(s in any_str(), mid in 0usize..=32) {
            let mid = floor_oracle(&s, mid);
            prop_assert_eq!(str::split_at(&s, mid), s.split_at(mid));
        }

        #[test]
        fn test_split_at_checked(s in any_str(), mid in 0usize..=32) {
            prop_assert_eq!(str::split_at_checked(&s, mid), s.split_at_checked(mid).inject());
        }

        #[test]
        fn test_is_ascii(s in any_str()) {
            prop_assert_eq!(str::is_ascii(&s), s.is_ascii());
        }

        #[test]
        fn test_eq_ignore_ascii_case(pair in case_pair()) {
            prop_assert_eq!(
                str::eq_ignore_ascii_case(&pair.0, &pair.1),
                pair.0.eq_ignore_ascii_case(&pair.1)
            );
        }

        #[test]
        fn test_eq_ignore_ascii_case_unrelated(a in any_str(), b in any_str()) {
            prop_assert_eq!(str::eq_ignore_ascii_case(&a, &b), a.eq_ignore_ascii_case(&b));
        }

        #[test]
        fn test_trim_ascii_start(s in ws_str()) {
            prop_assert_eq!(str::trim_ascii_start(&s), s.trim_ascii_start());
        }

        #[test]
        fn test_trim_ascii_end(s in ws_str()) {
            prop_assert_eq!(str::trim_ascii_end(&s), s.trim_ascii_end());
        }

        #[test]
        fn test_trim_ascii(s in ws_str()) {
            prop_assert_eq!(str::trim_ascii(&s), s.trim_ascii());
        }

        #[test]
        fn test_str_eq(a in any_str(), b in any_str()) {
            prop_assert_eq!(
                <core::primitive::str as crate::cmp::PartialEq<core::primitive::str>>::eq(&a, &b),
                a == b
            );
        }

        // Equal lengths, so the byte loop decides.
        #[test]
        fn test_str_eq_same_len(pairs in prop::collection::vec((any::<char>(), any::<bool>()), 0..=6)) {
            let a: String = pairs.iter().map(|p| p.0).collect();
            let b: String = pairs.iter().map(|p| if p.1 { p.0 } else { 'x' }).collect();
            prop_assert_eq!(
                <core::primitive::str as crate::cmp::PartialEq<core::primitive::str>>::eq(&a, &b),
                a == b
            );
        }

        #[test]
        fn test_parse_bool(s in prop::sample::select(vec!["true", "false", "TRUE", "", "true "])) {
            prop_assert_eq!(str::parse::<bool>(s), s.parse::<bool>().inject());
        }

        #[test]
        fn test_parse_bool_arbitrary(s in any_str()) {
            prop_assert_eq!(str::parse::<bool>(&s), s.parse::<bool>().inject());
        }

        // `from_utf8` is opaque, so the model error is built from std's.
        #[test]
        fn test_utf8_error_accessors(bytes in prop::collection::vec(any::<u8>(), 0..=8)) {
            let Err(e) = std::str::from_utf8(&bytes) else { return Ok(()) };
            let model = Utf8Error {
                valid_up_to: e.valid_up_to(),
                error_len: e.error_len().map(|l| l as u8).inject(),
            };
            prop_assert_eq!(Utf8Error::valid_up_to(&model), e.valid_up_to());
            prop_assert_eq!(Utf8Error::error_len(&model), e.error_len().inject());
        }
    }

    #[test]
    fn test_utf8_error_pinned() {
        let e = std::str::from_utf8(&[b'a', 0xFF]).unwrap_err();
        let model = Utf8Error {
            valid_up_to: 1,
            error_len: ModelOption::Some(1),
        };
        assert_eq!(e.valid_up_to(), 1);
        assert_eq!(e.error_len(), Some(1));
        assert_eq!(Utf8Error::valid_up_to(&model), 1);
        assert_eq!(Utf8Error::error_len(&model), ModelOption::Some(1));
    }

    #[test]
    fn test_utf8_error_truncated_pinned() {
        let e = std::str::from_utf8(&[b'a', 0xE2, 0x82]).unwrap_err();
        let model = Utf8Error {
            valid_up_to: 1,
            error_len: ModelOption::None,
        };
        assert_eq!(e.valid_up_to(), 1);
        assert_eq!(e.error_len(), None);
        assert_eq!(Utf8Error::valid_up_to(&model), 1);
        assert_eq!(Utf8Error::error_len(&model), ModelOption::None);
    }

    #[test]
    fn test_parse_bool_err() {
        assert_eq!(str::parse::<bool>("yes"), ModelResult::Err(ParseBoolError));
        assert!("yes".parse::<bool>().is_err());
    }

    // Runs the model's `PartialEq`, not the derived one.
    #[test]
    fn test_parse_bool_error_model_eq() {
        assert!(crate::cmp::PartialEq::eq(&ParseBoolError, &ParseBoolError));
    }

    #[test]
    fn test_split_at_off_boundary_panics() {
        // "é" is two bytes, so index 1 is inside it.
        crate::testing::panics_like_core(|| str::split_at("é", 1), || "é".split_at(1));
    }

    #[test]
    fn test_split_at_past_end_panics() {
        crate::testing::panics_like_core(|| str::split_at("abc", 4), || "abc".split_at(4));
    }

    /// std's `ceil_char_boundary` is unstable, so only the model is checked.
    #[test]
    #[should_panic]
    fn test_ceil_char_boundary_past_end_panics() {
        str::ceil_char_boundary("abc", 4);
    }
}
