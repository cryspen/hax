//! Equivalence tests for `core::iter::*`.
//!
//! These mirror the proptest block in `core-models/src/core/iter.rs`.
//! Most `IteratorMethods` proptests use closures (`map`, `filter`, `fold`,
//! `all`, `any`, `find`, `position`, …) and are skipped here pending
//! closure-extraction support. We keep the closure-free observations
//! (`count`, simple loops over a range) since those exercise the trait
//! plumbing without crossing the `Fn`-as-type-universe boundary.

use rust_lean_test_macro::rust_lean_test;

// ----- count over Range<usize> ----------------------------------------------

// TODO(range-count-extraction: `Range::count` reaches the same missing `Step` instance.)
/*
#[rust_lean_test]
pub fn test_range_count_zero() -> bool {
    (0..0usize).count() == 0
}
*/

// TODO(range-count-extraction: `Range::count` reaches the same missing `Step` instance.)
/*
#[rust_lean_test]
pub fn test_range_count_five() -> bool {
    (0..5usize).count() == 5
}
*/

// TODO(range-count-extraction: `Range::count` reaches the same missing `Step` instance.)
/*
#[rust_lean_test]
pub fn test_range_count_offset() -> bool {
    (3..10usize).count() == 7
}
*/

// ----- skipped: closure-based iterator combinators --------------------------

// TODO(slice-iter-extraction): closure-based iterator combinators like
// `fold` extract through Aeneas, but they bottom out in `slice::Iter::fold`
// (and friends) which are missing from the extracted Lean. Tried
// `[1u32,2,3,4].iter().fold(0u32, |acc, &x| acc + x)` — Aeneas emits the
// closure fine, then Lean fails with
//   `Unknown constant CoreModels.core.slice.Slice.iter`
//   `Unknown constant CoreModels.core.slice.iter.Iter.Insts...fold`.
// Revisit once slice iterators are modelled.
// pub fn test_fold_sum() -> bool {
//     let v = [1u32, 2, 3, 4];
//     v.iter().fold(0u32, |acc, &x| acc + x) == 10
// }

// TODO(slice-iter-extraction): `Iterator::map` / `Iterator::filter` /
// `Iterator::any` / `Iterator::all` / `Iterator::find` /
// `Iterator::find_map` / `Iterator::position` / `Iterator::for_each` /
// `Iterator::reduce` all take closures. Aeneas handles the closure side
// (see `core::array::test_from_fn_identity`), but on slice iterators they
// bottom out in `slice::Iter::*` which is missing from the model — same
// blocker as `fold` above.
// pub fn test_map_collect_sum() -> bool {
//     let v = [1u32, 2, 3];
//     v.iter().map(|x| x + 1).fold(0u32, |a, b| a + b) == (2 + 3 + 4)
// }
// pub fn test_filter_count() -> bool {
//     let v = [1u32, 2, 3, 4, 5];
//     v.iter().filter(|x| **x > 2).count() == 3
// }
// pub fn test_all_true() -> bool { [1u32, 2, 3].iter().all(|x| *x > 0) }
// pub fn test_any_true() -> bool { [1u32, 2, 3].iter().any(|x| *x == 2) }
// pub fn test_find_some() -> bool {
//     [1u32, 2, 3].iter().find(|x| **x == 2).copied() == Some(2)
// }
// pub fn test_position_some() -> bool {
//     [10u32, 20, 30].iter().position(|x| *x == 20) == Some(1)
// }

// `core::iter::from_fn` builds an iterator from a closure. Aeneas extracts
// the closure, but the resulting `iter::FromFn` adapter is not modelled, so
// any observation (`count`, `fold`, etc.) hits an unknown-constant error in
// Lean. Revisit once `iter::FromFn` is added to the model.
// pub fn test_from_fn() -> bool { ... }

// TODO(slice-iter-extraction): `[T; N]::iter()` / `[T]::iter()` produce a
// `slice::Iter` whose `next` takes `&mut self`; pure `count()` over them
// goes through `IteratorMethods::count`, which uses a while-let loop that
// the model marks `#[hax_lib::opaque]`. Revisit once opaque iterator
// methods get a concrete Lean spec.
// pub fn test_array_iter_count() -> bool {
//     [1u8, 2, 3].iter().count() == 3
// }

// TODO(adapter-extraction): `enumerate`, `step_by`, `take`, `skip`, `zip`,
// `chain`, `flatten`, `flat_map` build adapter structs whose iteration
// machinery is opaque in the model.
// pub fn test_take_count() -> bool { (0..100usize).take(5).count() == 5 }
// pub fn test_skip_count() -> bool { (0..10usize).skip(3).count() == 7 }
// pub fn test_enumerate_count() -> bool { (0..4usize).enumerate().count() == 4 }
// pub fn test_zip_count() -> bool {
//     (0..3usize).zip(0..5usize).count() == 3
// }
// pub fn test_chain_count() -> bool {
//     (0..3usize).chain(0..2usize).count() == 5
// }

// TODO(closure-extraction + Ord): `min` / `max` walk the iterator with a
// while-let loop using `Ord::cmp`; the loop body is opaque in the model.
// pub fn test_min() -> bool { ... }
// pub fn test_max() -> bool { ... }

// TODO(iter-last): `Iterator::last` uses a while-let loop; opaque in the
// model.
// pub fn test_last() -> bool { ... }

// TODO(iter-nth): `Iterator::nth` uses a for-loop that generates
// `Rust_primitives.Hax.Folds`, causing the dependency cycle the model
// avoids by marking the helper opaque.
// pub fn test_nth() -> bool { ... }
