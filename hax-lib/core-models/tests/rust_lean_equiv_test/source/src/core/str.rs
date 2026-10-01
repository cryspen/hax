//! Equivalence tests for `core::str::*`. `Pattern`-taking methods are not modeled.
//!
//! TODO(aeneas-string-literal): literals must be printable ASCII, since aeneas
//! mis-escapes other bytes; multi-byte UTF-8 is covered by the model's proptests.

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

// No `!=`: one use makes aeneas break every `PartialEq` impl in the crate.
#[rust_lean_test]
pub fn test_str_partial_eq_different_len() -> bool {
    ("abc" == "ab") == false
}

#[rust_lean_test]
pub fn test_str_partial_eq_same_len_different() -> bool {
    ("abc" == "abd") == false
}

#[rust_lean_test]
pub fn test_str_partial_eq_empty() -> bool {
    "" == ""
}

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
