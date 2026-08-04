//! Equivalence tests for `core::cmp::*`.

use rust_lean_test_macro::rust_lean_test;

// ----- u8: PartialEq::eq -----------------------------------------------------

#[rust_lean_test]
pub fn test_int_eq_same() -> bool {
    (0u8 == 0u8) == true
}

#[rust_lean_test]
pub fn test_int_eq_diff() -> bool {
    (0u8 == u8::MAX) == false
}

#[rust_lean_test]
pub fn test_int_eq_max_max() -> bool {
    (u8::MAX == u8::MAX) == true
}

// ----- u8: != ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_int_neq_same() -> bool {
    (0u8 != 0u8) == false
}

#[rust_lean_test]
pub fn test_int_neq_diff() -> bool {
    (0u8 != u8::MAX) == true
}

// ----- u8: < (lt) ------------------------------------------------------------

#[rust_lean_test]
pub fn test_int_lt_true() -> bool {
    (0u8 < u8::MAX) == true
}

#[rust_lean_test]
pub fn test_int_lt_equal() -> bool {
    (7u8 < 7u8) == false
}

#[rust_lean_test]
pub fn test_int_lt_false() -> bool {
    (u8::MAX < 0u8) == false
}

// ----- u8: <= (le) -----------------------------------------------------------

#[rust_lean_test]
pub fn test_int_le_true() -> bool {
    (0u8 <= u8::MAX) == true
}

#[rust_lean_test]
pub fn test_int_le_equal() -> bool {
    (7u8 <= 7u8) == true
}

#[rust_lean_test]
pub fn test_int_le_false() -> bool {
    (u8::MAX <= 0u8) == false
}

// ----- u8: > (gt) ------------------------------------------------------------

#[rust_lean_test]
pub fn test_int_gt_true() -> bool {
    (u8::MAX > 0u8) == true
}

#[rust_lean_test]
pub fn test_int_gt_equal() -> bool {
    (7u8 > 7u8) == false
}

#[rust_lean_test]
pub fn test_int_gt_false() -> bool {
    (0u8 > u8::MAX) == false
}

// ----- u8: >= (ge) -----------------------------------------------------------

#[rust_lean_test]
pub fn test_int_ge_true() -> bool {
    (u8::MAX >= 0u8) == true
}

#[rust_lean_test]
pub fn test_int_ge_equal() -> bool {
    (7u8 >= 7u8) == true
}

#[rust_lean_test]
pub fn test_int_ge_false() -> bool {
    (0u8 >= u8::MAX) == false
}

// ----- u8::partial_cmp -------------------------------------------------------

// TODO(partial-cmp-option): partial_cmp on integers returns
// `Option<Ordering>` whose `Some(Ordering::_)` shape involves both the
// option type (fine, helpers exist) AND the Ordering variant. We test the
// downstream `is_lt` / `is_eq` / `is_gt` predicates above instead; matching
// on `Option<Ordering>` directly needs more care to keep types pinned.

// ----- u8: Ord::cmp ----------------------------------------------------------
// Directly exercises the scalar `Ord` instance (`U8.Insts.CoreCmpOrd`),
// extracted from the `int_impls!` block in `core-models/src/core/cmp.rs`.

#[rust_lean_test]
pub fn test_u8_cmp_less() -> bool {
    match 3u8.cmp(&7u8) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_u8_cmp_greater() -> bool {
    match 9u8.cmp(&2u8) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_u8_cmp_equal() -> bool {
    match 5u8.cmp(&5u8) {
        std::cmp::Ordering::Equal => true,
        _ => false,
    }
}

// ----- wider unsigned: Ord::cmp / PartialEq::eq ------------------------------
// `int_impls!` generates one impl per integer type and each extracts to its
// own Lean def, so a type-indexed slip (wrong width, wrong instance) would
// not show up in the `u8` tests above.

#[rust_lean_test]
pub fn test_u32_cmp_less() -> bool {
    match 3u32.cmp(&7u32) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_u32_cmp_max_greater() -> bool {
    match u32::MAX.cmp(&0u32) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_u32_eq_max() -> bool {
    (u32::MAX == u32::MAX) == true
}

#[rust_lean_test]
pub fn test_usize_cmp_equal() -> bool {
    match 5usize.cmp(&5usize) {
        std::cmp::Ordering::Equal => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_usize_cmp_max_greater() -> bool {
    match usize::MAX.cmp(&1usize) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

// ----- signed: Ord::cmp ------------------------------------------------------
// These pin *signed* ordering. The model compares the dereferenced values, so
// the extracted Lean bodies use `<` / `>` on `Std.I8` / `Std.I32`; comparing
// the underlying bit patterns instead would flip every one of these (as two's
// complement, `-1i8` is `0xFF` and `i8::MIN` is `0x80`, both of which sit
// *above* the positive operands when read as unsigned).

#[rust_lean_test]
pub fn test_i8_cmp_negative_less_than_positive() -> bool {
    match (-1i8).cmp(&1i8) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i8_cmp_min_less_than_max() -> bool {
    match i8::MIN.cmp(&i8::MAX) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i8_cmp_min_less_than_zero() -> bool {
    match i8::MIN.cmp(&0i8) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i8_cmp_both_negative() -> bool {
    match (-5i8).cmp(&-3i8) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i8_cmp_negative_equal() -> bool {
    match (-7i8).cmp(&-7i8) {
        std::cmp::Ordering::Equal => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i32_cmp_positive_greater_than_negative() -> bool {
    match 1i32.cmp(&-1i32) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_i32_cmp_min_less_than_max() -> bool {
    match i32::MIN.cmp(&i32::MAX) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

// ----- signed: PartialEq::eq -------------------------------------------------

#[rust_lean_test]
pub fn test_i8_eq_negative_same() -> bool {
    (-7i8 == -7i8) == true
}

#[rust_lean_test]
pub fn test_i8_eq_min_max() -> bool {
    (i8::MIN == i8::MAX) == false
}

// ----- signed: comparison operators ------------------------------------------

#[rust_lean_test]
pub fn test_i8_lt_negative() -> bool {
    (i8::MIN < 0i8) == true
}

#[rust_lean_test]
pub fn test_i8_gt_negative() -> bool {
    (-1i8 > i8::MIN) == true
}

#[rust_lean_test]
pub fn test_i32_le_negative_equal() -> bool {
    (-5i32 <= -5i32) == true
}

#[rust_lean_test]
pub fn test_i32_ge_across_zero() -> bool {
    (0i32 >= -1i32) == true
}
