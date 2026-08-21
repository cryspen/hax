//! Equivalence tests for `core::ops::*`.
//!
//! Covers the arithmetic-assign operators, `ControlFlow`, `Bound` and the
//! range types' bound/containment queries.
//!
//! On the Rust side we use the `+=` / `-=` operators (which dispatch
//! through `AddAssign` / `SubAssign`); on the Lean side Aeneas
//! extracts the same operations against the model's impls.
//!
//! All values are kept inside the precondition ranges (no overflow,
//! lhs >= rhs).
//!
//! Several `core::ops` items the model provides are still `#[unstable]` in the
//! pinned toolchain's `core` (`Bound::{as_mut, copied}`,
//! `ControlFlow::{break_ok, continue_ok, into_value}`, `RangeBounds::is_empty`,
//! `IntoBounds`, `OneSidedRange`). Calling them here would mean putting a
//! `#![feature(...)]` on this crate, which charon would then also have to
//! accept, so they are exercised only by the proptests in
//! `core-models/src/core/ops.rs`.

use crate::helpers;
use core::ops::{Bound, RangeBounds, RangeInclusive};
use rust_lean_test_macro::rust_lean_test;

// =============================================================================
// AddAssign on u8 (precondition: x + y <= u8::MAX, mirrored from
// the proptest's `0u8..128` range bound on both operands)
// =============================================================================

#[rust_lean_test]
pub fn test_add_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x += 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_zero_plus_one() -> bool {
    let mut x: u8 = 0;
    x += 1u8;
    x == 1u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_mid() -> bool {
    let mut x: u8 = 42;
    x += 58u8;
    x == 100u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_boundary() -> bool {
    // The proptest constrains both operands to `0..128`, so 127 + 127
    // is the largest sum we can express (= 254, just under u8::MAX).
    let mut x: u8 = 127;
    x += 127u8;
    x == 254u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_lhs_zero() -> bool {
    let mut x: u8 = 0;
    x += 127u8;
    x == 127u8
}

// =============================================================================
// SubAssign on u8 (precondition: lhs >= rhs)
// =============================================================================

#[rust_lean_test]
pub fn test_sub_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x -= 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_self() -> bool {
    let mut x: u8 = 42;
    x -= 42u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_mid() -> bool {
    let mut x: u8 = 100;
    x -= 42u8;
    x == 58u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_zero() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 0u8;
    x == u8::MAX
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_one() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 1u8;
    x == 254u8
}

// =============================================================================
// ControlFlow::is_break / is_continue
// =============================================================================

#[rust_lean_test]
pub fn test_control_flow_is_break_on_break() -> bool {
    helpers::control_flow_break_u8(7).is_break() == true
}

#[rust_lean_test]
pub fn test_control_flow_is_break_on_continue() -> bool {
    helpers::control_flow_continue_u8(0).is_break() == false
}

#[rust_lean_test]
pub fn test_control_flow_is_continue_on_continue() -> bool {
    helpers::control_flow_continue_u8(u8::MAX).is_continue() == true
}

#[rust_lean_test]
pub fn test_control_flow_is_continue_on_break() -> bool {
    helpers::control_flow_break_u8(0).is_continue() == false
}

// =============================================================================
// ControlFlow::break_value / continue_value
// =============================================================================

#[rust_lean_test]
pub fn test_control_flow_break_value_on_break() -> bool {
    match helpers::control_flow_break_u8(u8::MAX).break_value() {
        Some(b) => b == u8::MAX,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_control_flow_break_value_on_continue() -> bool {
    match helpers::control_flow_continue_u8(3).break_value() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_control_flow_continue_value_on_continue() -> bool {
    match helpers::control_flow_continue_u8(0).continue_value() {
        Some(c) => c == 0u8,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_control_flow_continue_value_on_break() -> bool {
    match helpers::control_flow_break_u8(3).continue_value() {
        Some(_) => false,
        None => true,
    }
}

// ----- ControlFlow::map_break / map_continue ---------------------------------
//
// TODO(closure-extraction): both take a closure, which extracts poorly.
//
// #[rust_lean_test]
// pub fn test_control_flow_map_break() -> bool {
//     let cf: ControlFlow<u8, u8> = ControlFlow::Break(7);
//     match cf.map_break(|b| b + 1) {
//         ControlFlow::Break(b) => b == 8u8,
//         ControlFlow::Continue(_) => false,
//     }
// }
//
// #[rust_lean_test]
// pub fn test_control_flow_map_continue() -> bool {
//     let cf: ControlFlow<u8, u8> = ControlFlow::Continue(7);
//     match cf.map_continue(|c| c + 1) {
//         ControlFlow::Continue(c) => c == 8u8,
//         ControlFlow::Break(_) => false,
//     }
// }

// =============================================================================
// Bound::as_ref
// =============================================================================

#[rust_lean_test]
pub fn test_bound_as_ref_included() -> bool {
    let b: Bound<u8> = Bound::Included(7);
    match b.as_ref() {
        Bound::Included(x) => *x == 7u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_bound_as_ref_excluded_max() -> bool {
    let b: Bound<u8> = Bound::Excluded(u8::MAX);
    match b.as_ref() {
        Bound::Excluded(x) => *x == u8::MAX,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_bound_as_ref_unbounded() -> bool {
    match helpers::bound_unbounded_u8().as_ref() {
        Bound::Unbounded => true,
        _ => false,
    }
}

// ----- Bound::map ------------------------------------------------------------
//
// TODO(closure-extraction): `map` takes a closure, which extracts poorly.
//
// #[rust_lean_test]
// pub fn test_bound_map_included() -> bool {
//     let b: Bound<u8> = Bound::Included(7);
//     match b.map(|x| x + 1) {
//         Bound::Included(x) => x == 8u8,
//         _ => false,
//     }
// }

// ----- Bound::cloned ---------------------------------------------------------
//
// TODO(clone-by-value): the model's `Clone::clone` consumes `self`, so its
// `cloned` maps `Bound<T> -> Bound<T>` instead of real core's
// `Bound<&T> -> Bound<T>`; the impl is hidden from Aeneas, so the extraction of
// a call to it has no Lean definition to land on.
//
// #[rust_lean_test]
// pub fn test_bound_cloned_included() -> bool {
//     let x: u8 = 7;
//     match Bound::Included(&x).cloned() {
//         Bound::Included(v) => v == 7u8,
//         _ => false,
//     }
// }

// =============================================================================
// RangeBounds::start_bound / end_bound
// =============================================================================

#[rust_lean_test]
pub fn test_range_start_bound() -> bool {
    match (3u8..5u8).start_bound() {
        Bound::Included(x) => *x == 3u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_end_bound() -> bool {
    match (3u8..5u8).end_bound() {
        Bound::Excluded(x) => *x == 5u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_from_start_bound() -> bool {
    match (0u8..).start_bound() {
        Bound::Included(x) => *x == 0u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_from_end_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::end_bound(&(0u8..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..5u8)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_end_bound() -> bool {
    match (..u8::MAX).end_bound() {
        Bound::Excluded(x) => *x == u8::MAX,
        _ => false,
    }
}

// One `match` per test: binding two of them with `let` and combining them makes
// Aeneas's interpreter fail on the `Bound` result.
#[rust_lean_test]
pub fn test_range_full_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_full_end_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::end_bound(&(..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_inclusive_start_bound() -> bool {
    match RangeInclusive::new(3u8, 5u8).start_bound() {
        Bound::Included(x) => *x == 3u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_inclusive_end_bound_is_included() -> bool {
    match RangeInclusive::new(3u8, 5u8).end_bound() {
        Bound::Included(x) => *x == 5u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_inclusive_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..=5u8)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_inclusive_end_bound() -> bool {
    match (..=5u8).end_bound() {
        Bound::Included(x) => *x == 5u8,
        _ => false,
    }
}

// ----- RangeBounds::contains -------------------------------------------------
//
// TODO(trait-defaults): `contains` is a trait *default* in real core, which hax
// cannot express; the model provides it through the blanket-implemented
// `RangeBoundsDefaults` companion trait, so a call to
// `core::ops::RangeBounds::contains` has no Lean counterpart. The inherent
// `Range::contains` (tested below) is the reachable form.
//
// #[rust_lean_test]
// pub fn test_range_bounds_contains() -> bool {
//     RangeBounds::contains(&(3u8..5u8), &4u8) == true
// }

// =============================================================================
// Range::contains / Range::is_empty
// =============================================================================

#[rust_lean_test]
pub fn test_range_contains_inside() -> bool {
    (3u8..5u8).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_contains_start_is_included() -> bool {
    (3u8..5u8).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_contains_end_is_excluded() -> bool {
    (3u8..5u8).contains(&5u8) == false
}

#[rust_lean_test]
pub fn test_range_contains_below() -> bool {
    (3u8..5u8).contains(&0u8) == false
}

#[rust_lean_test]
pub fn test_range_contains_max() -> bool {
    (0u8..u8::MAX).contains(&u8::MAX) == false
}

#[rust_lean_test]
pub fn test_range_is_empty_nonempty() -> bool {
    (3u8..5u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_is_empty_equal_bounds() -> bool {
    (3u8..3u8).is_empty() == true
}

#[rust_lean_test]
pub fn test_range_is_empty_reversed() -> bool {
    (5u8..3u8).is_empty() == true
}

#[rust_lean_test]
pub fn test_range_is_empty_full_u8() -> bool {
    (0u8..u8::MAX).is_empty() == false
}

// =============================================================================
// RangeFrom::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_from_contains_above() -> bool {
    (3u8..).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_from_contains_start() -> bool {
    (3u8..).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_from_contains_below() -> bool {
    (3u8..).contains(&2u8) == false
}

#[rust_lean_test]
pub fn test_range_from_contains_max() -> bool {
    (0u8..).contains(&u8::MAX) == true
}

// =============================================================================
// RangeTo::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_to_contains_below() -> bool {
    (..5u8).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_to_contains_end_is_excluded() -> bool {
    (..5u8).contains(&5u8) == false
}

#[rust_lean_test]
pub fn test_range_to_contains_zero() -> bool {
    (..5u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_to_contains_nothing_when_end_is_zero() -> bool {
    (..0u8).contains(&0u8) == false
}

// =============================================================================
// RangeToInclusive::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_end() -> bool {
    (..=5u8).contains(&5u8) == true
}

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_zero() -> bool {
    (..=0u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_above() -> bool {
    (..=5u8).contains(&6u8) == false
}

// =============================================================================
// RangeInclusive::new / into_inner / contains / is_empty
// =============================================================================

#[rust_lean_test]
pub fn test_range_inclusive_new_into_inner() -> bool {
    let (start, end) = RangeInclusive::new(3u8, 5u8).into_inner();
    start == 3u8 && end == 5u8
}

#[rust_lean_test]
pub fn test_range_inclusive_into_inner_edges() -> bool {
    let (start, end) = (0u8..=u8::MAX).into_inner();
    start == 0u8 && end == u8::MAX
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_end() -> bool {
    (3u8..=5u8).contains(&5u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_start() -> bool {
    (3u8..=5u8).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_above() -> bool {
    (3u8..=5u8).contains(&6u8) == false
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_singleton() -> bool {
    (0u8..=0u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_nonempty() -> bool {
    (3u8..=5u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_singleton() -> bool {
    (3u8..=3u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_reversed() -> bool {
    (5u8..=3u8).is_empty() == true
}

// ----- RangeInclusive::start / RangeInclusive::end ---------------------------
//
// TODO(lean-name-clash): Aeneas would name these `RangeInclusive.start` /
// `RangeInclusive.«end»`, which are already the extracted structure's field
// projections, so they are hidden from Aeneas (see `core-models/src/core/ops.rs`)
// and have no Lean definition to land on. The proptests cover them.
//
// #[rust_lean_test]
// pub fn test_range_inclusive_start_end() -> bool {
//     let range = RangeInclusive::new(3u8, 5u8);
//     *range.start() == 3u8 && *range.end() == 5u8
// }

// ----- DerefMut / IndexMut ---------------------------------------------------
//
// The model declares both traits but no model type implements them (their only
// methods return `&mut`, which the F* backend does not support), so there is no
// concrete observation to pin here. The proptests in
// `core-models/src/core/ops.rs` exercise them against test-local impls.
