//! Model of `core::str`, restricted to the *byte-oriented* part of the API.
//!
//! Everything here goes through `rust_primitives::string::str_as_bytes`, which
//! matches how both backends see a `str`: aeneas represents it as `Slice U8`,
//! and hax as an abstract F* `string` (the `str` module is extracted
//! interface-only, see `CORE_MODELS_FSTAR_INTERFACES` in the Makefile).
//!
//! What is *not* here, and why:
//!   - every `Pattern`-taking method (`starts_with`, `find`, `split`,
//!     `trim_matches`, `strip_prefix`, …): aeneas cannot translate real
//!     `core`'s `Pattern` trait — its `Searcher` GAT hits `Unimplemented`
//!     (`core/src/str/pattern.rs:99`) — and that aborts the extraction of any
//!     *client* crate that calls one. Modeling them with a `&str`-only
//!     signature would score coverage but stay unusable end to end.
//!   - anything `char`-shaped (`chars`, `char_indices`, `Chars`, `Lines`,
//!     `EncodeUtf16`, `Escape*`, `Utf8Chunks`, `Utf8Pattern`): `core::char` is
//!     not modeled at all.
//!   - `from_utf8` and friends stay opaque: deciding UTF-8 validity needs a
//!     validation model this module does not have.
//!   - the `&mut str` half (`as_bytes_mut`, `split_at_mut`, `get_mut`,
//!     `make_ascii_lowercase`/`uppercase`, `from_utf8_mut`) and every
//!     `*_unchecked` / `from_raw_parts` entry point.
#![allow(non_camel_case_types)]

use crate::option::Option;
use rust_primitives::slice::{slice_index, slice_length};
use rust_primitives::string::{str_as_bytes, str_sub_bytes};

/// Stand-in for the `str` primitive: Rust forbids inherent impls on primitives,
/// so the `str::*` methods hang off this dummy the way `slice::Slice` does for
/// `[T]`. Each method takes the `str` it operates on as its first argument.
/// See [`std::primitive::str`]
// F*-only: `charon::exclude` would drop this dummy type while its `impl`
// blocks still reference it (see f32.rs).
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct str;

/// `b` is one of the five bytes `u8::is_ascii_whitespace` accepts (space, tab,
/// line feed, form feed, carriage return — vertical tab is *not* one of them).
fn is_ascii_whitespace_byte(b: core::primitive::u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D
}

/// ASCII-only `to_lowercase` on a single byte; non-ASCII bytes pass through.
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
    /// See [`std::primitive::str::is_char_boundary`]. A byte index is a
    /// boundary unless it points at a UTF-8 continuation byte (`0b10xxxxxx`).
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
            // Scan forward keeping the last boundary at or below `index`; a
            // backward scan would need a decreasing loop, which extracts worse.
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
    fn trim_ascii_end(s: &core::primitive::str) -> &core::primitive::str {
        let bytes = Self::as_bytes(s);
        let n = slice_length(bytes);
        let mut end = 0;
        for i in 0..n {
            if !is_ascii_whitespace_byte(*slice_index(bytes, i)) {
                end = i + 1;
            }
        }
        str_sub_bytes(s, 0, end)
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

/// `PartialEq<str> for str`, in its own submodule (as `slice::equality` is) so
/// that `str::traits`, which uses it, does not depend on the parent `str`
/// module — which itself depends on `str::traits` through `str::parse`. F*
/// rejects that as a module cycle.
pub mod equality {
    use super::str;
    use rust_primitives::slice::{slice_index, slice_length};

    /// `str` compares as its UTF-8 bytes.
    // The byte comparison is spelled out rather than delegated to
    // `<[u8] as PartialEq<[u8]>>::eq`: from an impl whose `Self` is the `str`
    // primitive, aeneas fails to resolve that nested dictionary
    // ("Could not find: trait_impl_id").
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
    // opaque: deciding UTF-8 validity needs a `char`/UTF-8 model we do not have.
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

pub mod error {
    use crate::option::Option;

    /// See [`std::str::Utf8Error`]. The fields are `pub(super)` (private in real
    /// `core`) so the model's own tests can build one — `from_utf8` is opaque
    /// here, so nothing in the model itself ever populates them.
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct Utf8Error {
        pub(super) valid_up_to: usize,
        pub(super) error_len: Option<u8>,
    }

    impl Utf8Error {
        /// Build one from what `rust_primitives::string::str_from_utf8` reports;
        /// `error_len == 0` is its encoding of `None`.
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

    /// See [`std::str::ParseBoolError`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct ParseBoolError;

    /// Always `true` like std's derived instance — the type carries no payload.
    /// F* compares structurally, so this is aeneas/lean only.
    #[cfg(not(hax_backend_fstar))]
    impl crate::cmp::PartialEq<ParseBoolError> for ParseBoolError {
        fn eq(&self, _other: &Self) -> bool {
            true
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

    // opaque for F*: the body compares against `"true"`/`"false"` through
    // `PartialEq for str`, whose instance F* cannot resolve from this module
    // (`Could not solve typeclass constraint Core_models.Bundle.t_PartialEq
    // Prims.string Prims.string`) — and hax mangles the two literals into
    // `"r#true"`/`"r#false"`, so the extracted body would be wrong anyway.
    // Keeping it a `val` also keeps `str::traits` from depending on the parent
    // `str` module, which F* would reject as a module cycle.
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

    /// Arbitrary (possibly multi-byte) strings, so the char-boundary and
    /// `is_ascii` paths see non-ASCII input.
    fn any_str() -> impl Strategy<Value = String> {
        prop::collection::vec(any::<char>(), 0..=8).prop_map(|cs| cs.into_iter().collect())
    }

    /// Strings drawn from an alphabet of the five ASCII-whitespace bytes, the
    /// vertical tab (which is *not* ASCII whitespace), letters and a multi-byte
    /// char, to exercise the `trim_ascii*` boundaries.
    fn ws_str() -> impl Strategy<Value = String> {
        prop::collection::vec(
            prop::sample::select(vec![
                ' ', '\t', '\n', '\r', '\u{0c}', '\u{0b}', 'a', 'Z', 'é',
            ]),
            0..=8,
        )
        .prop_map(|cs| cs.into_iter().collect())
    }

    /// Pairs that agree up to ASCII case often enough for
    /// `eq_ignore_ascii_case` to see its `true` branch.
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

    /// The largest char boundary `<= index` (`floor_char_boundary`'s spec).
    /// std's own method is unstable (`round_char_boundary`).
    fn floor_oracle(s: &core::primitive::str, index: usize) -> usize {
        (0..=index.min(s.len()))
            .rev()
            .find(|i| s.is_char_boundary(*i))
            .unwrap()
    }

    /// The smallest char boundary `>= index`, for `index <= s.len()`.
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
        // `mid` is snapped down to a char boundary: `split_at` panics off one,
        // and random indices into multi-byte strings almost never land on one.
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

        // Equal-length pairs make the per-byte comparison, not the length
        // shortcut, the deciding factor.
        #[test]
        fn test_str_eq_same_len(pairs in prop::collection::vec((any::<char>(), any::<bool>()), 0..=6)) {
            let a: String = pairs.iter().map(|p| p.0).collect();
            let b: String = pairs.iter().map(|p| if p.1 { p.0 } else { 'x' }).collect();
            prop_assert_eq!(
                <core::primitive::str as crate::cmp::PartialEq<core::primitive::str>>::eq(&a, &b),
                a == b
            );
        }

        // `parse` is exercised at `bool`: the model's only other `FromStr` impl
        // (`u64`) is opaque.
        #[test]
        fn test_parse_bool(s in prop::sample::select(vec!["true", "false", "TRUE", "", "true "])) {
            prop_assert_eq!(str::parse::<bool>(s), s.parse::<bool>().inject());
        }

        #[test]
        fn test_parse_bool_arbitrary(s in any_str()) {
            prop_assert_eq!(str::parse::<bool>(&s), s.parse::<bool>().inject());
        }

        // `from_utf8` is opaque, so nothing in the model builds a `Utf8Error`.
        // The accessors are checked against a `Utf8Error` assembled from what
        // real `core` reports for the same invalid input.
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

    /// `Utf8Error`'s accessors on hand-computed field values: `0xFF` is never a
    /// valid UTF-8 leading byte, so the error starts after the `a` and covers
    /// one byte.
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

    /// A truncated multi-byte sequence at the end of the input has no
    /// `error_len`.
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

    #[test]
    fn test_split_at_off_boundary_panics() {
        // "é" is two bytes, so index 1 is inside it.
        crate::testing::panics_like_core(|| str::split_at("é", 1), || "é".split_at(1));
    }

    #[test]
    fn test_split_at_past_end_panics() {
        crate::testing::panics_like_core(|| str::split_at("abc", 4), || "abc".split_at(4));
    }

    /// std's `ceil_char_boundary` is unstable (`round_char_boundary`), so only
    /// the model side can be observed here; std panics on the same input.
    #[test]
    #[should_panic]
    fn test_ceil_char_boundary_past_end_panics() {
        str::ceil_char_boundary("abc", 4);
    }
}
