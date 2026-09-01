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

// ----- clamp / Ordering::then / Ordering::then_with ---------------------------

#[rust_lean_test]
pub fn test_ordering_then_keeps_first() -> bool {
    match std::cmp::Ordering::Less.then(std::cmp::Ordering::Greater) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_ordering_then_falls_through_on_equal() -> bool {
    match std::cmp::Ordering::Equal.then(std::cmp::Ordering::Greater) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_ordering_is_le() -> bool {
    std::cmp::Ordering::Less.is_le() && std::cmp::Ordering::Equal.is_le()
}

#[rust_lean_test]
pub fn test_ordering_is_gt() -> bool {
    std::cmp::Ordering::Greater.is_gt() && !std::cmp::Ordering::Equal.is_gt()
}

// ----- minmax ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_minmax_ordered() -> bool {
    std::cmp::minmax(3u8, 7u8) == [3, 7]
}

#[rust_lean_test]
pub fn test_minmax_reversed() -> bool {
    std::cmp::minmax(7u8, 3u8) == [3, 7]
}

// On `Equal`, `minmax` keeps the argument order.
#[rust_lean_test]
pub fn test_minmax_equal() -> bool {
    std::cmp::minmax(5u8, 5u8) == [5, 5]
}

#[rust_lean_test]
pub fn test_minmax_extremes() -> bool {
    std::cmp::minmax(u8::MAX, 0u8) == [0, u8::MAX]
}

// ----- Rust-only: `Ord`'s default methods --------------------------------
// The model's `Ord` has only `cmp`; `max`/`min`/`clamp` are trait defaults in
// core, which hax cannot express, so they live in the model's separate
// `OrdDefaults` trait. `x.max(y)` in this crate resolves to `core::cmp::Ord`,
// which has no counterpart to extract against.
#[cfg(test)]
mod ord_defaults {
    #[test]
    fn test_max_first() {
        assert_eq!(9u8.max(2), 9);
    }

    #[test]
    fn test_max_second() {
        assert_eq!(2u8.max(9), 9);
    }

    #[test]
    fn test_max_extremes() {
        assert_eq!(0u8.max(u8::MAX), u8::MAX);
    }

    #[test]
    fn test_min_first() {
        assert_eq!(2u8.min(9), 2);
    }

    #[test]
    fn test_min_extremes() {
        assert_eq!(u8::MAX.min(0), 0);
    }

    #[test]
    fn test_clamp_below() {
        assert_eq!(1u8.clamp(3, 7), 3);
    }

    #[test]
    fn test_clamp_inside() {
        assert_eq!(5u8.clamp(3, 7), 5);
    }

    #[test]
    fn test_clamp_above() {
        assert_eq!(9u8.clamp(3, 7), 7);
    }
}

// ----- Rust-only: the closure-taking `*_by` / `*_by_key` family -----------
// TODO(closure-extraction): `max_by`, `min_by`, `max_by_key`, `min_by_key`,
// `minmax_by` and `minmax_by_key` all take a closure, which extracts poorly
// (same reason as `Option::map` in `core::option`). The pairs below differ only
// in their second component, so they compare `Equal` under the comparator —
// which is what pins the tie-breaks (`min*` keeps the first argument, `max*` the
// second).
#[cfg(test)]
mod by_and_by_key {
    #[test]
    fn test_max_by_ties_to_second() {
        assert_eq!(
            std::cmp::max_by((1u8, 10u8), (1u8, 20u8), |a, b| a.0.cmp(&b.0)),
            (1, 20)
        );
    }

    #[test]
    fn test_min_by_ties_to_first() {
        assert_eq!(
            std::cmp::min_by((1u8, 10u8), (1u8, 20u8), |a, b| a.0.cmp(&b.0)),
            (1, 10)
        );
    }

    #[test]
    fn test_max_by_picks_greater() {
        assert_eq!(
            std::cmp::max_by((1u8, 10u8), (2u8, 20u8), |a, b| a.0.cmp(&b.0)),
            (2, 20)
        );
    }

    #[test]
    fn test_max_by_key_ties_to_second() {
        assert_eq!(
            std::cmp::max_by_key((1u8, 10u8), (1u8, 20u8), |a| a.0),
            (1, 20)
        );
    }

    #[test]
    fn test_min_by_key_ties_to_first() {
        assert_eq!(
            std::cmp::min_by_key((1u8, 10u8), (1u8, 20u8), |a| a.0),
            (1, 10)
        );
    }

    #[test]
    fn test_min_by_key_picks_smaller() {
        assert_eq!(
            std::cmp::min_by_key((3u8, 10u8), (2u8, 20u8), |a| a.0),
            (2, 20)
        );
    }

    #[test]
    fn test_minmax_by_ties_keep_order() {
        assert_eq!(
            std::cmp::minmax_by((1u8, 10u8), (1u8, 20u8), |a, b| a.0.cmp(&b.0)),
            [(1, 10), (1, 20)]
        );
    }

    #[test]
    fn test_minmax_by_sorts() {
        assert_eq!(
            std::cmp::minmax_by((5u8, 10u8), (2u8, 20u8), |a, b| a.0.cmp(&b.0)),
            [(2, 20), (5, 10)]
        );
    }

    #[test]
    fn test_minmax_by_key_sorts() {
        assert_eq!(
            std::cmp::minmax_by_key((5u8, 10u8), (2u8, 20u8), |a| a.0),
            [(2, 20), (5, 10)]
        );
    }
}
