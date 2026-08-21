//! Equivalence tests for `alloc::vec::Vec::*`.
//!
//! Mirrors the proptest cases in `alloc/src/lib.rs` (module `vec::tests`),
//! pinning each observation on a concrete input.
//!
//! Notes on what's tested:
//! - Indexing `v[i]` is in `ALLOC_CHARON_EXCLUDES` (see top-level `Makefile`),
//!   so we verify per-element contents by sequential `pop()`s instead of
//!   `v[i] == x`.

use crate::helpers::Bumped;
use rust_lean_test_macro::rust_lean_test;

// ----- new -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_new_len_zero() -> bool {
    let v: Vec<u8> = Vec::new();
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_new_is_empty() -> bool {
    let v: Vec<u8> = Vec::new();
    v.is_empty()
}

// ----- with_capacity ---------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_with_capacity_zero_len() -> bool {
    let v: Vec<u8> = Vec::with_capacity(0);
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_with_capacity_ten_len() -> bool {
    let v: Vec<u8> = Vec::with_capacity(10);
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_with_capacity_is_empty() -> bool {
    let v: Vec<u8> = Vec::with_capacity(100);
    v.is_empty()
}

// ----- len -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_len_empty() -> bool {
    let v: Vec<u8> = Vec::new();
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_len_one() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(42);
    v.len() == 1
}

#[rust_lean_test]
pub fn test_vec_len_from_elem() -> bool {
    let v: Vec<u8> = vec![3u8; 5];
    v.len() == 5
}

#[rust_lean_test]
pub fn test_vec_len_from_elem_zero() -> bool {
    let v: Vec<u8> = vec![0u8; 0];
    v.len() == 0
}

// ----- is_empty --------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_is_empty_new() -> bool {
    let v: Vec<u8> = Vec::new();
    v.is_empty() == true
}

#[rust_lean_test]
pub fn test_vec_is_empty_after_push() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.is_empty() == false
}

// ----- as_slice --------------------------------------------------------------
//
// `as_slice` returns `&[T]`. We can observe it through length-via-deref
// (Vec implements Deref<Target=[T]>) but `len` on a slice is the same
// as `Vec::len`, so we mostly exercise that `as_slice` is well-typed.

#[rust_lean_test]
pub fn test_vec_as_slice_empty_len() -> bool {
    let v: Vec<u8> = Vec::new();
    v.as_slice().len() == 0
}

#[rust_lean_test]
pub fn test_vec_as_slice_one_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(9);
    v.as_slice().len() == 1
}

#[rust_lean_test]
pub fn test_vec_as_slice_three_len() -> bool {
    let v: Vec<u8> = vec![4u8; 3];
    v.as_slice().len() == 3
}

// ----- push ------------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_push_one_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.len() == 1
}

#[rust_lean_test]
pub fn test_vec_push_many_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.len() == 3
}

// ----- append ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_append_both_empty() -> bool {
    let mut a: Vec<u8> = Vec::new();
    let mut b: Vec<u8> = Vec::new();
    a.append(&mut b);
    a.len() == 0 && b.len() == 0
}

#[rust_lean_test]
pub fn test_vec_append_empty_to_nonempty() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(1);
    a.push(2);
    let mut b: Vec<u8> = Vec::new();
    a.append(&mut b);
    a.len() == 2 && b.len() == 0
}

// ----- extend_from_slice -----------------------------------------------------

#[rust_lean_test]
pub fn test_vec_extend_from_slice_empty_to_empty() -> bool {
    let mut v: Vec<u8> = Vec::new();
    let s: [u8; 0] = [];
    v.extend_from_slice(&s);
    v.len() == 0
}

// Clones each element, so the appended value is `Bumped(1).clone()`.
#[rust_lean_test]
pub fn test_vec_extend_from_slice_applies_clone() -> bool {
    let mut v: Vec<Bumped> = Vec::new();
    v.extend_from_slice(&[Bumped(1)]);
    match v.pop() {
        Some(b) => b.0 == 2,
        None => false,
    }
}

// ----- from_elem (`vec![x; n]`) ---------------------------------------------

#[rust_lean_test]
pub fn test_vec_from_elem_zero_len() -> bool {
    let v: Vec<u8> = vec![9u8; 0];
    v.len() == 0 && v.is_empty()
}

// std clones all but the last element, so this is `[Bumped(2), Bumped(1)]`.
#[rust_lean_test]
pub fn test_vec_from_elem_applies_clone() -> bool {
    let mut v: Vec<Bumped> = vec![Bumped(1); 2];
    match v.pop() {
        Some(last) => match v.pop() {
            Some(first) => last.0 == 1 && first.0 == 2,
            None => false,
        },
        None => false,
    }
}

// ----- index (excluded) ------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_index_first() -> bool {
    let v: Vec<u8> = vec![7u8; 1];
    v[0] == 7
}

#[rust_lean_test]
pub fn test_vec_index_range() -> bool {
    let v: Vec<u8> = vec![7u8; 3];
    v[0..2].len() == 2
}

// ----- sort_by (excluded) ----------------------------------------------------

// TODO(vec-index-excluded): Vec::sort_by is in ALLOC_CHARON_EXCLUDES (closure
// extraction is unsupported).

// ----- from_iter (excluded) --------------------------------------------------

// TODO(vec-index-excluded): Vec::from_iter is in ALLOC_CHARON_EXCLUDES.

// ----- remove ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_remove_only_element() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    let x = v.remove(0);
    x == 7 && v.is_empty()
}

// ----- swap_remove -----------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_swap_remove_only_element() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(9);
    let x = v.swap_remove(0);
    x == 9 && v.is_empty()
}

#[rust_lean_test]
pub fn test_vec_swap_remove_back() -> bool {
    // Removing the last element: no swap happens, so this behaves like `pop`.
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let x = v.swap_remove(2);
    x == 3 && v.len() == 2 && v[0] == 1 && v[1] == 2
}

#[rust_lean_test]
pub fn test_vec_swap_remove_front_moves_last() -> bool {
    // The case that distinguishes `swap_remove` from `remove`: the last
    // element takes the removed slot rather than everything shifting down.
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    let x = v.swap_remove(0);
    x == 1 && v.len() == 3 && v[0] == 4 && v[1] == 2 && v[2] == 3
}

#[rust_lean_test]
pub fn test_vec_swap_remove_middle() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let x = v.swap_remove(1);
    x == 2 && v.len() == 2 && v[0] == 1 && v[1] == 3
}

// ----- truncate / resize / clear ---------------------------------------------

#[rust_lean_test]
pub fn test_vec_truncate_shortens() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.truncate(1);
    v.len() == 1 && v[0] == 1
}

#[rust_lean_test]
pub fn test_vec_truncate_longer_is_noop() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.truncate(5);
    v.len() == 2 && v[0] == 1 && v[1] == 2
}

#[rust_lean_test]
pub fn test_vec_truncate_zero_empties() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.truncate(0);
    v.is_empty()
}

#[rust_lean_test]
pub fn test_vec_clear_empties() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.clear();
    v.is_empty()
}

#[rust_lean_test]
pub fn test_vec_resize_grows() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.resize(3, 7);
    v.len() == 3 && v[0] == 1 && v[1] == 7 && v[2] == 7
}

#[rust_lean_test]
pub fn test_vec_resize_shrinks() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.resize(1, 0);
    v.len() == 1 && v[0] == 1
}

#[rust_lean_test]
pub fn test_vec_resize_same_len_is_noop() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.resize(1, 9);
    v.len() == 1 && v[0] == 1
}

// ----- drain (iterator) ------------------------------------------------------

// Vec::drain ignores its `RangeBounds` argument, so it is `--opaque` for charon
// (see the Makefile) and has no Lean body to test against.

// ----- closure-using methods (excluded) --------------------------------------

// TODO(closure-extraction + vec-extraction-arity-mismatch): Vec::retain takes
// a closure. Aeneas can extract the closure (see core::array::from_fn) but
// every Vec method first trips on the arity-mismatch issue above. Revisit
// once Vec tests can compile in the first place.
// TODO(vec-iter-extraction): Vec::iter / Vec::into_iter use iterator traits
// whose Lean models we don't have yet.

// ----- pop -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_push_pop() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(9u8);
    match v.pop() {
        Some(x) => x == 9u8,
        None => false,
    }
}

// ----- PartialEq / Clone / IntoIterator on Vec (branch additions) ------------
// These exercise the extracted `eq_loop` / `clone_loop` / `IntoIter::next`.

#[rust_lean_test]
pub fn test_vec_eq_short_circuits() -> bool {
    // `Bumped::eq` panics on `u8::MAX`. std stops at the first mismatch, so the
    // second pair is never compared; a non-short-circuiting model would panic.
    let mut a: Vec<Bumped> = Vec::new();
    a.push(Bumped(1));
    a.push(Bumped(255));
    let mut b: Vec<Bumped> = Vec::new();
    b.push(Bumped(2));
    b.push(Bumped(255));
    (a == b) == false
}

#[rust_lean_test]
pub fn test_vec_eq_same() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(1u8);
    a.push(2u8);
    let mut b: Vec<u8> = Vec::new();
    b.push(1u8);
    b.push(2u8);
    (a == b) == true
}

#[rust_lean_test]
pub fn test_vec_eq_diff() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(1u8);
    let mut b: Vec<u8> = Vec::new();
    b.push(2u8);
    (a == b) == false
}

#[rust_lean_test]
pub fn test_vec_clone_preserves() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(3u8);
    a.push(4u8);
    let b = a.clone();
    (a == b) == true
}

#[rust_lean_test]
pub fn test_vec_into_iter_first() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7u8);
    v.push(8u8);
    let mut it = v.into_iter();
    match it.next() {
        Some(x) => x == 7u8,
        None => false,
    }
}

// ----- default ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_default_empty() -> bool {
    let a: Vec<u8> = Default::default();
    let b: Vec<u8> = Vec::new();
    (a == b) == true
}

// ----- capacity --------------------------------------------------------------
//
// The model's capacity is exact where std's is only a lower bound (see the
// `DEVIATION` note on `Vec::capacity`), so the observations below are limited to
// the cases where the two agree: a fresh `Vec`, a `vec![x; n]` (which std
// allocates exactly), and std's `capacity() >= len()` guarantee.

#[rust_lean_test]
pub fn test_vec_capacity_new_zero() -> bool {
    let v: Vec<u8> = Vec::new();
    v.capacity() == 0
}

#[rust_lean_test]
pub fn test_vec_capacity_from_elem_exact() -> bool {
    let v: Vec<u8> = vec![7u8; 3];
    v.capacity() == 3
}

#[rust_lean_test]
pub fn test_vec_capacity_at_least_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.capacity() >= v.len()
}

// ----- reserve / reserve_exact / shrink_to_fit / shrink_to -------------------

#[rust_lean_test]
pub fn test_vec_reserve_keeps_contents() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(5);
    v.reserve(100);
    match v.pop() {
        Some(x) => x == 5 && v.is_empty(),
        None => false,
    }
}

#[rust_lean_test]
pub fn test_vec_reserve_exact_keeps_len() -> bool {
    let mut v: Vec<u8> = vec![1u8; 2];
    v.reserve_exact(10);
    v.len() == 2
}

#[rust_lean_test]
pub fn test_vec_shrink_to_fit_capacity_is_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.shrink_to_fit();
    v.capacity() == v.len()
}

#[rust_lean_test]
pub fn test_vec_shrink_to_keeps_len() -> bool {
    let mut v: Vec<u8> = vec![3u8; 4];
    v.shrink_to(1);
    v.len() == 4
}

// ----- try_reserve / try_reserve_exact --------------------------------------

#[rust_lean_test]
pub fn test_vec_try_reserve_ok() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.try_reserve(10).is_ok()
}

#[rust_lean_test]
pub fn test_vec_try_reserve_exact_ok() -> bool {
    let mut v: Vec<u8> = vec![1u8; 1];
    v.try_reserve_exact(10).is_ok() && v.len() == 1
}

// ----- try_with_capacity -----------------------------------------------------

#[rust_lean_test]
pub fn test_vec_try_with_capacity_empty() -> bool {
    match Vec::<u8>::try_with_capacity(8) {
        Ok(v) => v.is_empty(),
        Err(_) => false,
    }
}

// ----- new_in / with_capacity_in / try_with_capacity_in ---------------------
//
// The model drops the allocator argument (see the `DEVIATION` note on
// `Vec::new_in`); only the resulting `Vec` is observable.

#[rust_lean_test]
pub fn test_vec_new_in_empty() -> bool {
    let v: Vec<u8> = Vec::new_in(std::alloc::Global);
    v.is_empty()
}

#[rust_lean_test]
pub fn test_vec_with_capacity_in_empty() -> bool {
    let v: Vec<u8> = Vec::with_capacity_in(4, std::alloc::Global);
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_try_with_capacity_in_empty() -> bool {
    match Vec::<u8>::try_with_capacity_in(4, std::alloc::Global) {
        Ok(v) => v.is_empty(),
        Err(_) => false,
    }
}

// ----- allocator -------------------------------------------------------------

// TODO(no-observable-result): `Vec::allocator`, `Drain::allocator`,
// `IntoIter::allocator` and `ExtractIf::allocator` all return the (zero-sized)
// global allocator, which real `alloc` gives no `PartialEq`/`Debug` for, so
// there is no `bool` observation to pin. They are covered by the property tests
// in `alloc/src/vec/tests.rs`.

// ----- as_mut_slice ----------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_as_mut_slice_len() -> bool {
    let mut v: Vec<u8> = vec![1u8; 3];
    v.as_mut_slice().len() == 3
}

#[rust_lean_test]
pub fn test_vec_as_mut_slice_empty() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.as_mut_slice().is_empty()
}

// ----- into_boxed_slice ------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_into_boxed_slice_len() -> bool {
    let v: Vec<u8> = vec![4u8; 3];
    v.into_boxed_slice().len() == 3
}

#[rust_lean_test]
pub fn test_vec_into_boxed_slice_empty() -> bool {
    let v: Vec<u8> = Vec::new();
    v.into_boxed_slice().is_empty()
}

// ----- try_remove ------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_try_remove_in_bounds() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    match v.try_remove(0) {
        Some(x) => x == 1 && v.len() == 1,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_vec_try_remove_out_of_bounds() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    match v.try_remove(1) {
        Some(_) => false,
        None => v.len() == 1,
    }
}

#[rust_lean_test]
pub fn test_vec_try_remove_empty() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.try_remove(0) == crate::helpers::none_u8()
}

// ----- push_mut / insert_mut -------------------------------------------------

#[rust_lean_test]
pub fn test_vec_push_mut_returns_pushed() -> bool {
    let mut v: Vec<u8> = Vec::new();
    let r = v.push_mut(9u8);
    *r == 9
}

#[rust_lean_test]
pub fn test_vec_push_mut_write_back() -> bool {
    let mut v: Vec<u8> = Vec::new();
    let r = v.push_mut(9u8);
    *r = 3;
    match v.pop() {
        Some(x) => x == 3,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_vec_insert_mut_front() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(2);
    let r = v.insert_mut(0, 1u8);
    *r == 1 && v.len() == 2
}

// ----- dedup -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_dedup_consecutive() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(1);
    v.push(2);
    v.dedup();
    v.len() == 2
}

#[rust_lean_test]
pub fn test_vec_dedup_non_consecutive_kept() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(1);
    v.dedup();
    v.len() == 3
}

#[rust_lean_test]
pub fn test_vec_dedup_empty() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.dedup();
    v.is_empty()
}

// Exercises the `PartialEq` dictionary: `Bumped`'s `eq` is not `u8`'s.
#[rust_lean_test]
pub fn test_vec_dedup_applies_partial_eq() -> bool {
    let mut v: Vec<Bumped> = Vec::new();
    v.push(Bumped(1));
    v.push(Bumped(1));
    v.push(Bumped(2));
    v.dedup();
    v.len() == 2
}

// ----- extend_from_within ----------------------------------------------------

// TODO(range-bounds-unmodeled): `Vec::extend_from_within` is generic over
// `RangeBounds<usize>`, and a client call site passes that dictionary. Neither
// `core::ops::RangeBounds` nor its impls are modeled (which is also why
// `Vec::drain` ignores its range), so the extracted call has both an unknown
// constant and one argument too many. Same blocker as `drain` below.
// pub fn test_vec_extend_from_within_full() -> bool {
//     let mut v: Vec<u8> = Vec::new();
//     v.push(1);
//     v.push(2);
//     v.extend_from_within(..);
//     v.len() == 4
// }

// ----- into_flattened --------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_into_flattened_len() -> bool {
    let mut v: Vec<[u8; 2]> = Vec::new();
    v.push([1, 2]);
    v.push([3, 4]);
    v.into_flattened().len() == 4
}

#[rust_lean_test]
pub fn test_vec_into_flattened_order() -> bool {
    let mut v: Vec<[u8; 2]> = Vec::new();
    v.push([1, 2]);
    v.push([3, 4]);
    let mut f = v.into_flattened();
    match f.pop() {
        Some(x) => x == 4,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_vec_into_flattened_empty() -> bool {
    let v: Vec<[u8; 2]> = Vec::new();
    v.into_flattened().is_empty()
}

// ----- Drain::as_slice -------------------------------------------------------

// TODO(range-bounds-unmodeled): reaching `Drain::as_slice` needs `Vec::drain`,
// whose extracted call site passes a `RangeBounds` dictionary and an explicit
// allocator type the model's `drain` does not take (see `extend_from_within`).
// pub fn test_vec_drain_as_slice_len() -> bool {
//     let mut v: Vec<u8> = vec![1u8; 3];
//     v.drain(..).as_slice().len() == 3
// }

// ----- IntoIter::as_slice / as_mut_slice -------------------------------------

#[rust_lean_test]
pub fn test_vec_into_iter_as_slice_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.into_iter().as_slice().len() == 2
}

#[rust_lean_test]
pub fn test_vec_into_iter_as_slice_after_next() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    let mut it = v.into_iter();
    it.next();
    it.as_slice().len() == 1
}

#[rust_lean_test]
pub fn test_vec_into_iter_as_mut_slice_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    let mut it = v.into_iter();
    it.as_mut_slice().len() == 1
}

// ----- closure-taking additions (not extracted) ------------------------------

// TODO(closure-extraction): `Vec::retain`, `retain_mut`, `dedup_by`,
// `dedup_by_key`, `resize_with`, `pop_if`, `extract_if` and `from_fn` all take a
// closure, which the equivalence tests cannot drive through Aeneas yet. Their
// property tests live in `alloc/src/vec/tests.rs`.

// ----- split_off -------------------------------------------------------------

#[rust_lean_test]
pub fn test_vec_split_off() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(1u8);
    a.push(2u8);
    a.push(3u8);
    let b = a.split_off(1);
    let mut ea: Vec<u8> = Vec::new();
    ea.push(1u8);
    let mut eb: Vec<u8> = Vec::new();
    eb.push(2u8);
    eb.push(3u8);
    (a == ea) && (b == eb)
}
