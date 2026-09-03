//! Equivalence tests for `core::iter::*`.
//!
//! These mirror the proptest block in `core-models/src/core/iter.rs`. The
//! provided methods reach Lean through the `Iterator::<m>.default` shims and the
//! per-impl specialisations in `CoreModels/Core/FunsEpilogue.lean`, which have no
//! Rust counterpart -- these guards are the only thing that checks them.
//!
//! The handful that stay Rust-only each carry a `TODO` naming their blocker.

use crate::helpers::{Keyed, keyed};
use rust_lean_test_macro::rust_lean_test;

// ----- count over Range<usize> ----------------------------------------------

#[rust_lean_test]
pub fn test_range_count_zero() -> bool {
    (0..0usize).count() == 0
}

#[rust_lean_test]
pub fn test_range_count_five() -> bool {
    (0..5usize).count() == 5
}

#[rust_lean_test]
pub fn test_range_count_offset() -> bool {
    (3..10usize).count() == 7
}

// ----- eager consumers -------------------------------------------------------

#[rust_lean_test]
pub fn test_range_fold_sum() -> bool {
    (1..5usize).fold(0usize, |acc, x| acc + x) == 10
}

#[rust_lean_test]
pub fn test_range_fold_empty_keeps_init() -> bool {
    (0..0usize).fold(7usize, |acc, x| acc + x) == 7
}

#[rust_lean_test]
pub fn test_range_last() -> bool {
    match (1..4usize).last() {
        Some(v) => v == 3,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_last_empty() -> bool {
    (0..0usize).last().is_none()
}

#[rust_lean_test]
pub fn test_range_min() -> bool {
    match (1..4usize).min() {
        Some(v) => v == 1,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_max() -> bool {
    match (1..4usize).max() {
        Some(v) => v == 3,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_min_empty() -> bool {
    (0..0usize).min().is_none()
}

#[rust_lean_test]
pub fn test_range_reduce() -> bool {
    match (1..5usize).reduce(|a, b| a + b) {
        Some(v) => v == 10,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_all_true() -> bool {
    (1..4usize).all(|x| x > 0)
}

#[rust_lean_test]
pub fn test_range_all_false() -> bool {
    (1..4usize).all(|x| x > 1) == false
}

#[rust_lean_test]
pub fn test_range_any_true() -> bool {
    (1..4usize).any(|x| x == 2)
}

#[rust_lean_test]
pub fn test_range_any_false() -> bool {
    (1..4usize).any(|x| x == 9) == false
}

#[rust_lean_test]
pub fn test_range_find_some() -> bool {
    match (1..4usize).find(|x| *x == 2) {
        Some(v) => v == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_find_none() -> bool {
    (1..4usize).find(|x| *x == 9).is_none()
}

#[rust_lean_test]
pub fn test_range_find_map() -> bool {
    match (1..4usize).find_map(|x| if x > 1 { Some(x * 10) } else { None }) {
        Some(v) => v == 20,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_position_some() -> bool {
    match (10..40usize).step_by(10).position(|x| x == 20) {
        Some(v) => v == 1,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_range_position_none() -> bool {
    (1..4usize).position(|x| x == 9).is_none()
}

// `min` keeps the first of several equal elements and `max` the last, and at
// `usize` the two are indistinguishable.
#[rust_lean_test]
pub fn test_min_keeps_the_first_of_a_tie() -> bool {
    let mut v: Vec<Keyed> = Vec::new();
    v.push(keyed(5, 1));
    v.push(keyed(1, 2));
    v.push(keyed(5, 3));
    v.push(keyed(1, 4));
    match v.into_iter().min() {
        Some(k) => k.tag == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_max_keeps_the_last_of_a_tie() -> bool {
    let mut v: Vec<Keyed> = Vec::new();
    v.push(keyed(5, 1));
    v.push(keyed(1, 2));
    v.push(keyed(5, 3));
    v.push(keyed(1, 4));
    match v.into_iter().max() {
        Some(k) => k.tag == 3,
        None => false,
    }
}

// ----- lazy adapters, drained by an eager consumer ---------------------------

#[rust_lean_test]
pub fn test_map_fold() -> bool {
    (1..4usize).map(|x| x + 1).fold(0usize, |a, b| a + b) == 9
}

#[rust_lean_test]
pub fn test_filter_count() -> bool {
    (1..6usize).filter(|x| *x > 2).count() == 3
}

#[rust_lean_test]
pub fn test_filter_map_fold() -> bool {
    (1..6usize)
        .filter_map(|x| if x % 2 == 0 { Some(x) } else { None })
        .fold(0usize, |a, b| a + b)
        == 6
}

#[rust_lean_test]
pub fn test_take_count() -> bool {
    (0..100usize).take(5).count() == 5
}

#[rust_lean_test]
pub fn test_take_past_the_end() -> bool {
    (0..3usize).take(10).count() == 3
}

#[rust_lean_test]
pub fn test_skip_count() -> bool {
    (0..10usize).skip(3).count() == 7
}

#[rust_lean_test]
pub fn test_skip_past_the_end() -> bool {
    (0..3usize).skip(10).count() == 0
}

#[rust_lean_test]
pub fn test_take_while_count() -> bool {
    (1..10usize).take_while(|x| *x < 4).count() == 3
}

#[rust_lean_test]
pub fn test_skip_while_count() -> bool {
    (1..10usize).skip_while(|x| *x < 4).count() == 6
}

#[rust_lean_test]
pub fn test_map_while_count() -> bool {
    (1..10usize)
        .map_while(|x| if x < 4 { Some(x) } else { None })
        .count()
        == 3
}

#[rust_lean_test]
pub fn test_step_by_fold() -> bool {
    (0..10usize).step_by(3).fold(0usize, |a, b| a + b) == 18
}

#[rust_lean_test]
pub fn test_enumerate_count() -> bool {
    (0..4usize).enumerate().count() == 4
}

#[rust_lean_test]
pub fn test_enumerate_fold_indices() -> bool {
    (7..10usize).enumerate().fold(0usize, |a, p| a + p.0) == 3
}

#[rust_lean_test]
pub fn test_zip_count_stops_at_the_shorter() -> bool {
    (0..3usize).zip(0..5usize).count() == 3
}

#[rust_lean_test]
pub fn test_chain_count() -> bool {
    (0..3usize).chain(0..2usize).count() == 5
}

#[rust_lean_test]
pub fn test_fuse_count() -> bool {
    (0..3usize).fuse().count() == 3
}

// TODO(closure-by-ref-extraction): `inspect` takes `FnMut(&Self::Item)`, and the
// generated closure instance does not type-check -- the same blocker as
// `Option::filter` and `Option::inspect`.
#[cfg(test)]
#[test]
fn test_inspect_passes_elements_through() {
    assert_eq!((1..4usize).inspect(|_x| ()).fold(0usize, |a, b| a + b), 6);
}

// TODO(flat-map-namespace): the extraction references
// `iter.adapters.flatten.FlatMap.Insts.…count` -- `FlatMap` under `flatten`'s
// namespace rather than `flat_map`'s -- and the application does not type-check.
#[cfg(test)]
#[test]
fn test_flat_map_count() {
    assert_eq!((0..3usize).flat_map(|_x| 0..2usize).count(), 6);
}

// ----- rev / DoubleEndedIterator ---------------------------------------------

// TODO(rev-slice-iter): `rev()` has no guard. `slice::Iter` and `Enumerate` are
// the only `DoubleEndedIterator`s the model has, and aeneas cannot translate
// std's `slice::Iter::find` ("a lifetime constraint relating a higher-ranked
// lifetime to a free lifetime"), which `Rev<Iter>` pulls in. `skip_lean` cannot
// apply: extraction fails before any guard is emitted.
#[cfg(test)]
#[test]
fn test_rev_first_is_the_last() {
    let a: [u8; 3] = [1, 2, 3];
    assert_eq!(a.as_slice().iter().rev().next(), Some(&3));
}

// ----- slice / array / Vec iterators -----------------------------------------

#[rust_lean_test]
pub fn test_slice_iter_count() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    a.as_slice().iter().count() == 3
}

#[rust_lean_test]
pub fn test_slice_iter_fold() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().iter().fold(0u8, |acc, x| acc + *x) == 10
}

#[rust_lean_test]
pub fn test_vec_into_iter_count() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.into_iter().count() == 2
}

// ----- collect ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_collect_into_vec_len() -> bool {
    let v: Vec<usize> = (0..3usize).collect();
    v.len() == 3
}

#[rust_lean_test]
pub fn test_collect_into_vec_preserves_order() -> bool {
    let v: Vec<usize> = (5..8usize).collect();
    v[0] == 5 && v[1] == 6 && v[2] == 7
}

#[rust_lean_test]
pub fn test_collect_into_vec_empty() -> bool {
    let v: Vec<usize> = (0..0usize).collect();
    v.len() == 0
}

// TODO(iter-nth-excluded): `iter_nth`'s helper carries `hax_lib::exclude` (a Lean
// forward reference to `core.Usize.Insts.CoreIterRangeStep`), so `nth` has no
// definition to elaborate against.
#[cfg(test)]
#[test]
fn test_nth() {
    assert_eq!((1..4usize).nth(1), Some(2));
}

// TODO(from-fn-missing): `core::iter::from_fn` is not modelled.
#[cfg(test)]
#[test]
fn test_from_fn() {
    let mut n = 0u32;
    let it = core::iter::from_fn(move || {
        n += 1;
        if n <= 3 { Some(n) } else { None }
    });
    assert_eq!(it.fold(0u32, |a, b| a + b), 6);
}
