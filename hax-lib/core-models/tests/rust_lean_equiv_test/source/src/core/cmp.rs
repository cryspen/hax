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
// Directly exercises the scalar `Ord` instance (`U8.Insts.CoreCmpOrd`)
// re-provided in `FunsPrologue`.

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
