//! Equivalence tests for `core::str::*` and the `str` primitive's methods.
//!
//! The model is byte-oriented throughout (aeneas represents `str` as
//! `Slice U8`), so the interesting boundaries are the multi-byte UTF-8
//! sequences: `"é"` is two bytes and `"€"` is three.
//!
//! Only *printable ASCII* (plus `\t`, `\n`, `\r`) may appear in a literal
//! here: aeneas prints any other byte of a string constant as `\NNN`, which is
//! not a valid Lean escape, so such a test does not elaborate at all. The
//! `TODO(aeneas-string-literal)` blocks below are the tests that fall foul of
//! that; multi-byte behaviour is covered by the proptests in
//! `core-models/src/core/str.rs` instead.
//!
//! Not covered here, and why:
//!   - every `Pattern`-taking method (`starts_with`, `find`, `split`,
//!     `trim_matches`, …) is absent from the model: charon puts real
//!     `core`'s `Pattern` trait in the client LLBC and aeneas aborts on its
//!     GAT (`Unimplemented`, `core/src/str/pattern.rs:99`), which kills the
//!     whole extraction of this crate — not just one test.
//!   - `floor_char_boundary` / `ceil_char_boundary` are modeled but unstable
//!     in std (`round_char_boundary`), so no stable client call exists to
//!     pin them; they are covered by the model crate's proptests only.
//!   - `str::as_str` is modeled but unstable in std (`str_as_str`), so it has
//!     no stable client call either; the model crate's proptest checks it
//!     against `String::as_str`.
//!   - `Utf8Error`'s accessors are modeled but unreachable from client code:
//!     `from_utf8` is opaque in the model, so nothing produces a
//!     `Utf8Error`. Same, proptests only.

use rust_lean_test_macro::rust_lean_test;

// ----- len -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_str_len_empty() -> bool {
    "".len() == 0
}

#[rust_lean_test]
pub fn test_str_len_one() -> bool {
    "a".len() == 1
}

#[rust_lean_test]
pub fn test_str_len_ascii() -> bool {
    "abc".len() == 3
}

// TODO(aeneas-string-literal): see the module docs.
// /// `len` counts bytes, not chars.
// #[rust_lean_test]
// pub fn test_str_len_two_byte_char() -> bool {
//     "é".len() == 2
// }

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_len_three_byte_char() -> bool {
//     "€".len() == 3
// }

// ----- is_empty --------------------------------------------------------------

#[rust_lean_test]
pub fn test_str_is_empty_true() -> bool {
    "".is_empty()
}

#[rust_lean_test]
pub fn test_str_is_empty_false() -> bool {
    !"a".is_empty()
}

// ----- as_bytes --------------------------------------------------------------

#[rust_lean_test]
pub fn test_str_as_bytes_empty() -> bool {
    "".as_bytes().len() == 0
}

#[rust_lean_test]
pub fn test_str_as_bytes_first() -> bool {
    "abc".as_bytes()[0] == 97u8
}

#[rust_lean_test]
pub fn test_str_as_bytes_last() -> bool {
    "abc".as_bytes()[2] == 99u8
}

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_as_bytes_two_byte_char() -> bool {
//     let b = "é".as_bytes();
//     b.len() == 2 && b[0] == 195u8 && b[1] == 169u8
// }

// ----- is_char_boundary ------------------------------------------------------

#[rust_lean_test]
pub fn test_str_is_char_boundary_zero() -> bool {
    "abc".is_char_boundary(0)
}

#[rust_lean_test]
pub fn test_str_is_char_boundary_zero_empty() -> bool {
    "".is_char_boundary(0)
}

#[rust_lean_test]
pub fn test_str_is_char_boundary_len() -> bool {
    "abc".is_char_boundary(3)
}

#[rust_lean_test]
pub fn test_str_is_char_boundary_past_end() -> bool {
    !"abc".is_char_boundary(4)
}

#[rust_lean_test]
pub fn test_str_is_char_boundary_inside_ascii() -> bool {
    "abc".is_char_boundary(1)
}

// TODO(aeneas-string-literal): see the module docs.
// /// Index 1 is the continuation byte of a two-byte sequence.
// #[rust_lean_test]
// pub fn test_str_is_char_boundary_inside_two_byte_char() -> bool {
//     !"é".is_char_boundary(1)
// }

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_is_char_boundary_inside_three_byte_char() -> bool {
//     !"€".is_char_boundary(1) && !"€".is_char_boundary(2) && "€".is_char_boundary(3)
// }

// ----- split_at --------------------------------------------------------------

#[rust_lean_test]
pub fn test_str_split_at_zero() -> bool {
    let (a, b) = "abc".split_at(0);
    a.is_empty() && b == "abc"
}

#[rust_lean_test]
pub fn test_str_split_at_len() -> bool {
    let (a, b) = "abc".split_at(3);
    a == "abc" && b.is_empty()
}

#[rust_lean_test]
pub fn test_str_split_at_middle() -> bool {
    let (a, b) = "abc".split_at(1);
    a == "a" && b == "bc"
}

#[rust_lean_test]
pub fn test_str_split_at_empty() -> bool {
    let (a, b) = "".split_at(0);
    a.is_empty() && b.is_empty()
}

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_split_at_before_two_byte_char() -> bool {
//     let (a, b) = "aé".split_at(1);
//     a == "a" && b == "é"
// }

// ----- split_at_checked ------------------------------------------------------

#[rust_lean_test]
pub fn test_str_split_at_checked_some() -> bool {
    match "abc".split_at_checked(1) {
        Some((a, b)) => a == "a" && b == "bc",
        None => false,
    }
}

#[rust_lean_test]
pub fn test_str_split_at_checked_past_end() -> bool {
    "abc".split_at_checked(4).is_none()
}

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_split_at_checked_off_boundary() -> bool {
//     "é".split_at_checked(1).is_none()
// }

#[rust_lean_test]
pub fn test_str_split_at_checked_len() -> bool {
    "abc".split_at_checked(3).is_some()
}

// ----- is_ascii --------------------------------------------------------------

#[rust_lean_test]
pub fn test_str_is_ascii_empty() -> bool {
    "".is_ascii()
}

#[rust_lean_test]
pub fn test_str_is_ascii_true() -> bool {
    "abc \t\n".is_ascii()
}

/// `~` is 0x7E, the last printable ASCII byte.
#[rust_lean_test]
pub fn test_str_is_ascii_tilde() -> bool {
    "~".is_ascii()
}

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_is_ascii_del() -> bool {
//     "\u{7f}".is_ascii()
// }

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_is_ascii_false() -> bool {
//     !"aé".is_ascii()
// }

// ----- eq_ignore_ascii_case --------------------------------------------------

#[rust_lean_test]
pub fn test_str_eq_ignore_ascii_case_same() -> bool {
    "abc".eq_ignore_ascii_case("ABC")
}

#[rust_lean_test]
pub fn test_str_eq_ignore_ascii_case_mixed() -> bool {
    "aBc".eq_ignore_ascii_case("AbC")
}

#[rust_lean_test]
pub fn test_str_eq_ignore_ascii_case_empty() -> bool {
    "".eq_ignore_ascii_case("")
}

#[rust_lean_test]
pub fn test_str_eq_ignore_ascii_case_different_len() -> bool {
    !"abc".eq_ignore_ascii_case("ab")
}

#[rust_lean_test]
pub fn test_str_eq_ignore_ascii_case_different() -> bool {
    !"abc".eq_ignore_ascii_case("abd")
}

// TODO(aeneas-string-literal): see the module docs.
// /// Non-ASCII bytes are compared as-is, so `é`/`É` (different UTF-8) differ.
// #[rust_lean_test]
// pub fn test_str_eq_ignore_ascii_case_non_ascii() -> bool {
//     !"é".eq_ignore_ascii_case("É")
// }

// ----- trim_ascii_start / trim_ascii_end / trim_ascii ------------------------

#[rust_lean_test]
pub fn test_str_trim_ascii_start_none() -> bool {
    "abc".trim_ascii_start() == "abc"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_start_some() -> bool {
    " \t\n\rabc".trim_ascii_start() == "abc"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_start_all_whitespace() -> bool {
    "   ".trim_ascii_start().is_empty()
}

#[rust_lean_test]
pub fn test_str_trim_ascii_start_empty() -> bool {
    "".trim_ascii_start().is_empty()
}

// TODO(aeneas-string-literal): see the module docs.
// /// The vertical tab is *not* ASCII whitespace.
// #[rust_lean_test]
// pub fn test_str_trim_ascii_start_vertical_tab() -> bool {
//     "\u{0b}a".trim_ascii_start() == "\u{0b}a"
// }

#[rust_lean_test]
pub fn test_str_trim_ascii_end_some() -> bool {
    "abc \t".trim_ascii_end() == "abc"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_end_all_whitespace() -> bool {
    "   ".trim_ascii_end().is_empty()
}

#[rust_lean_test]
pub fn test_str_trim_ascii_end_none() -> bool {
    "abc".trim_ascii_end() == "abc"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_both() -> bool {
    "  abc  ".trim_ascii() == "abc"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_inner_whitespace_kept() -> bool {
    " a b ".trim_ascii() == "a b"
}

#[rust_lean_test]
pub fn test_str_trim_ascii_empty() -> bool {
    "".trim_ascii().is_empty()
}

// ----- PartialEq for str -----------------------------------------------------

#[rust_lean_test]
pub fn test_str_partial_eq_same() -> bool {
    "abc" == "abc"
}

#[rust_lean_test]
pub fn test_str_partial_eq_different_len() -> bool {
    "abc" != "ab"
}

#[rust_lean_test]
pub fn test_str_partial_eq_same_len_different() -> bool {
    "abc" != "abd"
}

#[rust_lean_test]
pub fn test_str_partial_eq_empty() -> bool {
    "" == ""
}

// TODO(aeneas-string-literal): see the module docs.
// #[rust_lean_test]
// pub fn test_str_partial_eq_non_ascii() -> bool {
//     "é" == "é"
// }

// ----- parse / FromStr for bool ----------------------------------------------

#[rust_lean_test]
pub fn test_str_parse_bool_true() -> bool {
    match "true".parse::<bool>() {
        Ok(b) => b,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_str_parse_bool_false() -> bool {
    match "false".parse::<bool>() {
        Ok(b) => !b,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_str_parse_bool_err() -> bool {
    "TRUE".parse::<bool>().is_err()
}

#[rust_lean_test]
pub fn test_str_parse_bool_err_empty() -> bool {
    "".parse::<bool>().is_err()
}

#[rust_lean_test]
pub fn test_str_parse_bool_err_trailing_space() -> bool {
    "true ".parse::<bool>().is_err()
}
