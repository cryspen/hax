//! Equivalence tests for `[T]` (`core::slice`) operations.
//!
//! These mirror the proptest block in `core-models/src/core/slice.rs`.

use crate::helpers::Bumped;
use rust_lean_test_macro::rust_lean_test;

// ----- len -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_len_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().len() == 0
}

#[rust_lean_test]
pub fn test_len_one() -> bool {
    let a: [u8; 1] = [42];
    a.as_slice().len() == 1
}

#[rust_lean_test]
pub fn test_len_eight() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a.as_slice().len() == 8
}

// ----- is_empty --------------------------------------------------------------

#[rust_lean_test]
pub fn test_is_empty_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().is_empty()
}

#[rust_lean_test]
pub fn test_is_empty_one() -> bool {
    let a: [u8; 1] = [0];
    a.as_slice().is_empty() == false
}

#[rust_lean_test]
pub fn test_is_empty_many() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().is_empty() == false
}

// ----- contains --------------------------------------------------------------

#[rust_lean_test]
pub fn test_contains_present() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&3)
}

#[rust_lean_test]
pub fn test_contains_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&1)
}

#[rust_lean_test]
pub fn test_contains_absent() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&99) == false
}

#[rust_lean_test]
pub fn test_contains_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().contains(&0) == false
}

// `contains` stops at the first match, so `Bumped::eq` never sees `u8::MAX`
// — unless the model keeps comparing past it.
#[rust_lean_test]
pub fn test_contains_stops_at_first_match() -> bool {
    let a = [Bumped(1), Bumped(u8::MAX)];
    a.as_slice().contains(&Bumped(1))
}

// ----- split_at --------------------------------------------------------------

#[rust_lean_test]
pub fn test_split_at_zero() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(0);
    l.is_empty() && r.len() == 4
}

#[rust_lean_test]
pub fn test_split_at_full() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(4);
    l.len() == 4 && r.is_empty()
}

#[rust_lean_test]
pub fn test_split_at_middle_lens() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(2);
    l.len() == 2 && r.len() == 2
}

#[rust_lean_test]
pub fn test_split_at_middle_left_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, _r) = a.as_slice().split_at(2);
    l[0] == 1
}

#[rust_lean_test]
pub fn test_split_at_middle_right_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (_l, r) = a.as_slice().split_at(2);
    r[0] == 3
}

// ----- split_at_checked ------------------------------------------------------

#[rust_lean_test]
pub fn test_split_at_checked_in_range_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(2).is_some()
}

#[rust_lean_test]
pub fn test_split_at_checked_at_end_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(4).is_some()
}

#[rust_lean_test]
pub fn test_split_at_checked_out_of_range_none() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(5).is_none()
}

// ----- first -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_first_present() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().first() {
        Some(v) => *v == 10,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_first_some_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().first() {
        Some(v) => *v == 7,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_first_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().first().is_none()
}

// ----- last ------------------------------------------------------------------

#[rust_lean_test]
pub fn test_last_present() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().last() {
        Some(v) => *v == 40,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_last_some_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().last() {
        Some(v) => *v == 7,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_last_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().last().is_none()
}

// ----- get (usize) -----------------------------------------------------------

#[rust_lean_test]
pub fn test_get_usize_in_range() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().get(2) {
        Some(v) => *v == 30,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_get_usize_first() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().get(0) {
        Some(v) => *v == 10,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_get_usize_out_of_range() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    a.as_slice().get(4).is_none()
}

#[rust_lean_test]
pub fn test_get_usize_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().get(0).is_none()
}

// ----- starts_with / ends_with ----------------------------------------------

#[rust_lean_test]
pub fn test_starts_with_true() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [1, 2];
    a.as_slice().starts_with(needle.as_slice())
}

#[rust_lean_test]
pub fn test_starts_with_empty_needle() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 0] = [];
    a.as_slice().starts_with(needle.as_slice())
}

#[rust_lean_test]
pub fn test_starts_with_false() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [2, 3];
    a.as_slice().starts_with(needle.as_slice()) == false
}

#[rust_lean_test]
pub fn test_ends_with_true() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [3, 4];
    a.as_slice().ends_with(needle.as_slice())
}

#[rust_lean_test]
pub fn test_ends_with_empty_needle() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 0] = [];
    a.as_slice().ends_with(needle.as_slice())
}

#[rust_lean_test]
pub fn test_ends_with_false() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [2, 3];
    a.as_slice().ends_with(needle.as_slice()) == false
}

// ----- Range / RangeFrom indexing, get(range) --------------------------------

#[rust_lean_test]
pub fn test_index_range() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice()[1..3] == [2, 3]
}

#[rust_lean_test]
pub fn test_get_range_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().get(1..3).is_some()
}

#[rust_lean_test]
pub fn test_index_range_from() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice()[2..] == [3, 4]
}

// ----- swap / reverse (mutate through &mut [T]) ------------------------------

#[rust_lean_test]
pub fn test_slice_swap() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    s.swap(0, 2);
    a == [3u8, 2, 1]
}

#[rust_lean_test]
pub fn test_slice_reverse() -> bool {
    let mut a = [1u8, 2, 3, 4];
    let s: &mut [u8] = &mut a;
    s.reverse();
    a == [4u8, 3, 2, 1]
}

// Overwrites `dst` with *clones* of `src`'s elements.
#[rust_lean_test]
pub fn test_clone_from_slice_applies_clone() -> bool {
    let mut dst = [Bumped(0)];
    let src = [Bumped(1)];
    let d: &mut [Bumped] = &mut dst;
    d.clone_from_slice(&src);
    dst[0].0 == 2
}

#[rust_lean_test]
pub fn test_fill() -> bool {
    let mut a: [u8; 4] = [0, 0, 0, 0];
    let s: &mut [u8] = &mut a;
    s.fill(7);
    a == [7, 7, 7, 7]
}

// Rust-only: `slice::iter::Iter` does not translate (see `core::iter`).
#[cfg(test)]
#[test]
fn test_iter_count() {
    let a: [u8; 3] = [1, 2, 3];
    assert_eq!(a.as_slice().iter().count(), 3);
}

#[rust_lean_test]
pub fn test_binary_search() -> bool {
    let a: [u8; 4] = [1, 3, 5, 7];
    a.as_slice().binary_search(&5) == Ok(2)
}

// Rust-only: the model has no `RangeBounds` instance.
#[cfg(test)]
#[test]
fn test_copy_within() {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    let s: &mut [u8] = &mut a;
    s.copy_within(0..2, 2);
    assert_eq!(a, [1, 2, 1, 2]);
}

// ----------------------------------------------------------------------------
// `core::slice::index::*` is on `CHARON_EXCLUDES`, so the `SliceIndex`
// impls (for `usize`, `Range`, `RangeFrom`, `RangeTo`, `RangeFull`) are
// not extracted. The Lean side resolves through the name map to manual
// definitions. Each `Range*` variant routes through a distinct
// `SliceIndex` impl, so we test all of them.
// ----------------------------------------------------------------------------

// ----- s[i] (manually defined in Lean, not extracted) -----------------------

#[rust_lean_test]
pub fn test_slice_index_usize_first() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    s[0] == 10
}

#[rust_lean_test]
pub fn test_slice_index_usize_last() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    s[7] == 80
}

#[rust_lean_test]
pub fn test_slice_index_usize_middle() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    s[3] == 40
}

// ----- &s[..end] : RangeTo (manually defined in Lean, not extracted) --------

#[rust_lean_test]
pub fn test_slice_index_range_to_len() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t.len() == 3
}

#[rust_lean_test]
pub fn test_slice_index_range_to_first_elem() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t[0] == 10
}

#[rust_lean_test]
pub fn test_slice_index_range_to_last_elem() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t[2] == 30
}

// ----- &s[..] : RangeFull (manually defined in Lean, not extracted) ---------

#[rust_lean_test]
pub fn test_slice_index_range_full_len() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..];
    t.len() == 8
}

// ----- PartialEq / Ord on slices (branch additions) --------------------------

#[rust_lean_test]
pub fn test_slice_eq_same() -> bool {
    let a: &[u8] = &[1u8, 2, 3];
    let b: &[u8] = &[1u8, 2, 3];
    (a == b) == true
}

#[rust_lean_test]
pub fn test_slice_eq_diff() -> bool {
    let a: &[u8] = &[1u8, 2, 3];
    let b: &[u8] = &[1u8, 2, 4];
    (a == b) == false
}

// ----- Ord / PartialOrd on slices (lexicographic) ----------------------------
// These exercise the extracted `partial_cmp_loop` / `cmp_loop`.

#[rust_lean_test]
pub fn test_slice_cmp_less_by_elem() -> bool {
    let a: &[u8] = &[1, 2, 3];
    let b: &[u8] = &[1, 5, 0];
    match a.cmp(b) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_slice_cmp_less_by_len() -> bool {
    // `[1,2]` is a prefix of `[1,2,3]`, so it is `Less`.
    let a: &[u8] = &[1, 2];
    let b: &[u8] = &[1, 2, 3];
    match a.cmp(b) {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_slice_cmp_greater_by_elem() -> bool {
    let a: &[u8] = &[2];
    let b: &[u8] = &[1, 9, 9];
    match a.cmp(b) {
        std::cmp::Ordering::Greater => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_slice_cmp_equal() -> bool {
    let a: &[u8] = &[4, 5, 6];
    let b: &[u8] = &[4, 5, 6];
    match a.cmp(b) {
        std::cmp::Ordering::Equal => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_slice_partial_cmp_less() -> bool {
    let a: &[u8] = &[1, 2];
    let b: &[u8] = &[1, 3];
    match a.partial_cmp(b) {
        Some(std::cmp::Ordering::Less) => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_slice_eq_diff_len() -> bool {
    let a: &[u8] = &[1, 2];
    let b: &[u8] = &[1, 2, 3];
    (a == b) == false
}

// ----- get_unchecked (in-bounds) ---------------------------------------------
// In-bounds is the only defined behaviour; the model projects like `index`.

#[rust_lean_test]
pub fn test_slice_get_unchecked_first() -> bool {
    let s: &[u8] = &[10u8, 20, 30];
    unsafe { *s.get_unchecked(0) == 10 }
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_last() -> bool {
    let s: &[u8] = &[10u8, 20, 30];
    unsafe { *s.get_unchecked(2) == 30 }
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_range() -> bool {
    let s: &[u8] = &[10u8, 20, 30, 40];
    let sub: &[u8] = unsafe { s.get_unchecked(1..3) };
    let expected: &[u8] = &[20u8, 30];
    sub == expected
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_range_from() -> bool {
    let s: &[u8] = &[10u8, 20, 30, 40];
    let sub: &[u8] = unsafe { s.get_unchecked(2..) };
    let expected: &[u8] = &[30u8, 40];
    sub == expected
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_range_to() -> bool {
    let s: &[u8] = &[10u8, 20, 30, 40];
    let sub: &[u8] = unsafe { s.get_unchecked(..2) };
    let expected: &[u8] = &[10u8, 20];
    sub == expected
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_range_full() -> bool {
    let s: &[u8] = &[10u8, 20, 30, 40];
    let sub: &[u8] = unsafe { s.get_unchecked(..) };
    sub == s
}

// ----- get_mut / get_unchecked_mut (mutate through the &mut) -----------------

#[rust_lean_test]
pub fn test_slice_get_mut_usize() -> bool {
    let mut a = [10u8, 20, 30];
    let s: &mut [u8] = &mut a;
    if let Some(r) = s.get_mut(1) {
        *r = 99;
    }
    a == [10u8, 99, 30]
}

#[rust_lean_test]
pub fn test_slice_get_mut_usize_oob() -> bool {
    let mut a = [10u8, 20, 30];
    let s: &mut [u8] = &mut a;
    // out of bounds: `get_mut` returns `None`, leaving the slice unchanged
    s.get_mut(5).is_none() && a == [10u8, 20, 30]
}

#[rust_lean_test]
pub fn test_slice_get_unchecked_mut_usize() -> bool {
    let mut a = [10u8, 20, 30];
    let s: &mut [u8] = &mut a;
    unsafe {
        *s.get_unchecked_mut(2) = 99;
    }
    a == [10u8, 20, 99]
}

// ----- PartialEq<[T; N]> for [T]  (slice == array) ---------------------------

#[rust_lean_test]
pub fn test_slice_eq_array_true() -> bool {
    let s: &[u8] = &[1u8, 2, 3];
    *s == [1u8, 2, 3]
}

#[rust_lean_test]
pub fn test_slice_eq_array_false_value() -> bool {
    let s: &[u8] = &[1u8, 2, 3];
    (*s == [1u8, 2, 9]) == false
}

#[rust_lean_test]
pub fn test_slice_eq_array_false_len() -> bool {
    let s: &[u8] = &[1u8, 2];
    (*s == [1u8, 2, 3]) == false
}

// ----- chunks / chunks_exact / windows / copy_from_slice ---------------------

#[rust_lean_test]
pub fn test_chunks_first() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().chunks(2);
    match it.next() {
        Some(c) => {
            let e: &[u8] = &[1, 2];
            c == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_chunks_last_is_partial() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().chunks(2);
    it.next();
    it.next();
    match it.next() {
        Some(c) => {
            let e: &[u8] = &[5];
            c == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_chunks_exact_drops_remainder() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().chunks_exact(2);
    it.next();
    it.next();
    match it.next() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_windows_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let mut it = a.as_slice().windows(2);
    match it.next() {
        Some(w) => {
            let e: &[u8] = &[1, 2];
            w == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_windows_second_overlaps() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let mut it = a.as_slice().windows(2);
    it.next();
    match it.next() {
        Some(w) => {
            let e: &[u8] = &[2, 3];
            w == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_copy_from_slice() -> bool {
    let src: [u8; 3] = [7, 8, 9];
    let mut dst: [u8; 3] = [0, 0, 0];
    let d: &mut [u8] = &mut dst;
    d.copy_from_slice(&src);
    dst == [7, 8, 9]
}

// ----- split_first / split_last ----------------------------------------------

#[rust_lean_test]
pub fn test_split_first_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().split_first().is_none()
}

#[rust_lean_test]
pub fn test_split_first_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().split_first() {
        Some((v, rest)) => *v == 7 && rest.is_empty(),
        None => false,
    }
}

#[rust_lean_test]
pub fn test_split_first_many() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    match a.as_slice().split_first() {
        Some((v, rest)) => *v == 1 && rest.len() == 2 && rest[0] == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_split_last_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().split_last().is_none()
}

#[rust_lean_test]
pub fn test_split_last_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().split_last() {
        Some((v, rest)) => *v == 7 && rest.is_empty(),
        None => false,
    }
}

#[rust_lean_test]
pub fn test_split_last_many() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    match a.as_slice().split_last() {
        Some((v, rest)) => *v == 3 && rest.len() == 2 && rest[1] == 2,
        None => false,
    }
}

// ----- split_at_unchecked (in-bounds is the only defined behaviour) ----------

#[rust_lean_test]
pub fn test_split_at_unchecked_middle() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = unsafe { a.as_slice().split_at_unchecked(2) };
    l.len() == 2 && r.len() == 2 && l[0] == 1 && r[0] == 3
}

#[rust_lean_test]
pub fn test_split_at_unchecked_zero() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = unsafe { a.as_slice().split_at_unchecked(0) };
    l.is_empty() && r.len() == 4
}

#[rust_lean_test]
pub fn test_split_at_unchecked_full() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = unsafe { a.as_slice().split_at_unchecked(4) };
    l.len() == 4 && r.is_empty()
}

// ----- swap_unchecked --------------------------------------------------------

#[rust_lean_test]
pub fn test_swap_unchecked_ends() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    unsafe { s.swap_unchecked(0, 2) };
    a == [3u8, 2, 1]
}

#[rust_lean_test]
pub fn test_swap_unchecked_same_index() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    unsafe { s.swap_unchecked(1, 1) };
    a == [1u8, 2, 3]
}

// ----- rotate_left / rotate_right --------------------------------------------

#[rust_lean_test]
pub fn test_rotate_left_middle() -> bool {
    let mut a = [1u8, 2, 3, 4, 5];
    let s: &mut [u8] = &mut a;
    s.rotate_left(2);
    a == [3u8, 4, 5, 1, 2]
}

#[rust_lean_test]
pub fn test_rotate_left_zero() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    s.rotate_left(0);
    a == [1u8, 2, 3]
}

#[rust_lean_test]
pub fn test_rotate_left_full() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    s.rotate_left(3);
    a == [1u8, 2, 3]
}

#[rust_lean_test]
pub fn test_rotate_right_middle() -> bool {
    let mut a = [1u8, 2, 3, 4, 5];
    let s: &mut [u8] = &mut a;
    s.rotate_right(2);
    a == [4u8, 5, 1, 2, 3]
}

#[rust_lean_test]
pub fn test_rotate_right_empty() -> bool {
    let mut a: [u8; 0] = [];
    let s: &mut [u8] = &mut a;
    s.rotate_right(0);
    a.is_empty()
}

// ----- rchunks / rchunks_exact / remainder -----------------------------------

#[rust_lean_test]
pub fn test_rchunks_first_is_tail() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().rchunks(2);
    match it.next() {
        Some(c) => {
            let e: &[u8] = &[4, 5];
            c == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_rchunks_last_is_partial() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().rchunks(2);
    it.next();
    it.next();
    match it.next() {
        Some(c) => {
            let e: &[u8] = &[1];
            c == e
        }
        None => false,
    }
}

#[rust_lean_test]
pub fn test_rchunks_empty_none() -> bool {
    let a: [u8; 0] = [];
    let mut it = a.as_slice().rchunks(2);
    it.next().is_none()
}

#[rust_lean_test]
pub fn test_rchunks_exact_drops_front_remainder() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().rchunks_exact(2);
    it.next();
    it.next();
    it.next().is_none()
}

#[rust_lean_test]
pub fn test_rchunks_exact_first() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let mut it = a.as_slice().rchunks_exact(2);
    match it.next() {
        Some(c) => {
            let e: &[u8] = &[4, 5];
            c == e
        }
        None => false,
    }
}

// `rchunks_exact`'s remainder is at the *front*, `chunks_exact`'s at the back.
#[rust_lean_test]
pub fn test_rchunks_exact_remainder() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let e: &[u8] = &[1];
    a.as_slice().rchunks_exact(2).remainder() == e
}

#[rust_lean_test]
pub fn test_rchunks_exact_remainder_empty_when_exact() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().rchunks_exact(2).remainder().is_empty()
}

#[rust_lean_test]
pub fn test_chunks_exact_remainder() -> bool {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    let e: &[u8] = &[5];
    a.as_slice().chunks_exact(2).remainder() == e
}

#[rust_lean_test]
pub fn test_chunks_exact_remainder_empty_when_exact() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().chunks_exact(2).remainder().is_empty()
}

// ----- is_sorted -------------------------------------------------------------

#[rust_lean_test]
pub fn test_is_sorted_ascending() -> bool {
    let a: [u8; 4] = [1, 2, 2, 3];
    a.as_slice().is_sorted()
}

#[rust_lean_test]
pub fn test_is_sorted_descending_false() -> bool {
    let a: [u8; 3] = [3, 2, 1];
    a.as_slice().is_sorted() == false
}

#[rust_lean_test]
pub fn test_is_sorted_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().is_sorted()
}

#[rust_lean_test]
pub fn test_is_sorted_one() -> bool {
    let a: [u8; 1] = [7];
    a.as_slice().is_sorted()
}

// ----- split_off_first / split_off_last --------------------------------------

#[rust_lean_test]
pub fn test_split_off_first_some() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let mut s: &[u8] = a.as_slice();
    match s.split_off_first() {
        Some(v) => *v == 1 && s.len() == 2 && s[0] == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_split_off_first_empty_none() -> bool {
    let a: [u8; 0] = [];
    let mut s: &[u8] = a.as_slice();
    s.split_off_first().is_none() && s.is_empty()
}

#[rust_lean_test]
pub fn test_split_off_last_some() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let mut s: &[u8] = a.as_slice();
    match s.split_off_last() {
        Some(v) => *v == 3 && s.len() == 2 && s[1] == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_split_off_last_empty_none() -> bool {
    let a: [u8; 0] = [];
    let mut s: &[u8] = a.as_slice();
    s.split_off_last().is_none() && s.is_empty()
}

// ----- first_mut / last_mut --------------------------------------------------

#[rust_lean_test]
pub fn test_first_mut_writes() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    if let Some(r) = s.first_mut() {
        *r = 9;
    }
    a == [9u8, 2, 3]
}

#[rust_lean_test]
pub fn test_first_mut_empty_none() -> bool {
    let mut a: [u8; 0] = [];
    let s: &mut [u8] = &mut a;
    s.first_mut().is_none()
}

#[rust_lean_test]
pub fn test_last_mut_writes() -> bool {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    if let Some(r) = s.last_mut() {
        *r = 9;
    }
    a == [1u8, 2, 9]
}

#[rust_lean_test]
pub fn test_last_mut_empty_none() -> bool {
    let mut a: [u8; 0] = [];
    let s: &mut [u8] = &mut a;
    s.last_mut().is_none()
}

// ----- strip_prefix / strip_suffix / trim_prefix / trim_suffix ---------------

#[rust_lean_test]
pub fn test_strip_prefix_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let p: [u8; 2] = [1, 2];
    match a.as_slice().strip_prefix(p.as_slice()) {
        Some(rest) => rest.len() == 2 && rest[0] == 3,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_strip_prefix_empty_prefix() -> bool {
    let a: [u8; 2] = [1, 2];
    let p: [u8; 0] = [];
    match a.as_slice().strip_prefix(p.as_slice()) {
        Some(rest) => rest.len() == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_strip_prefix_none() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 2] = [2, 3];
    a.as_slice().strip_prefix(p.as_slice()).is_none()
}

#[rust_lean_test]
pub fn test_strip_prefix_whole() -> bool {
    let a: [u8; 2] = [1, 2];
    let p: [u8; 2] = [1, 2];
    match a.as_slice().strip_prefix(p.as_slice()) {
        Some(rest) => rest.is_empty(),
        None => false,
    }
}

#[rust_lean_test]
pub fn test_strip_suffix_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let p: [u8; 2] = [3, 4];
    match a.as_slice().strip_suffix(p.as_slice()) {
        Some(rest) => rest.len() == 2 && rest[0] == 1,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_strip_suffix_none() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 2] = [1, 2];
    a.as_slice().strip_suffix(p.as_slice()).is_none()
}

// `strip_prefix` takes a `SlicePattern`, so an array argument goes through a
// different impl than a slice one.
#[rust_lean_test]
pub fn test_strip_prefix_array_pattern() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 1] = [1];
    match a.as_slice().strip_prefix(&p) {
        Some(rest) => rest.len() == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_trim_prefix_present() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 1] = [1];
    a.as_slice().trim_prefix(p.as_slice()).len() == 2
}

#[rust_lean_test]
pub fn test_trim_prefix_absent_returns_original() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 1] = [9];
    a.as_slice().trim_prefix(p.as_slice()).len() == 3
}

#[rust_lean_test]
pub fn test_trim_suffix_present() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 1] = [3];
    a.as_slice().trim_suffix(p.as_slice()).len() == 2
}

#[rust_lean_test]
pub fn test_trim_suffix_absent_returns_original() -> bool {
    let a: [u8; 3] = [1, 2, 3];
    let p: [u8; 1] = [9];
    a.as_slice().trim_suffix(p.as_slice()).len() == 3
}

#[rust_lean_test]
pub fn test_strip_circumfix_both() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let p: [u8; 1] = [1];
    let q: [u8; 1] = [4];
    match a.as_slice().strip_circumfix(p.as_slice(), q.as_slice()) {
        Some(rest) => rest.len() == 2 && rest[0] == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_strip_circumfix_prefix_missing_none() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let p: [u8; 1] = [9];
    let q: [u8; 1] = [4];
    a.as_slice()
        .strip_circumfix(p.as_slice(), q.as_slice())
        .is_none()
}

// `Bumped::eq` is not the identity, so this catches a dropped `PartialEq`
// dictionary in the strip family.
#[rust_lean_test]
pub fn test_strip_prefix_uses_partial_eq() -> bool {
    let a = [Bumped(1), Bumped(2)];
    let p = [Bumped(1)];
    match a.as_slice().strip_prefix(p.as_slice()) {
        Some(rest) => rest.len() == 1,
        None => false,
    }
}

// ----- [u8] ASCII helpers ----------------------------------------------------

#[rust_lean_test]
pub fn test_is_ascii_true() -> bool {
    let a: [u8; 3] = [65, 66, 127];
    a.as_slice().is_ascii()
}

#[rust_lean_test]
pub fn test_is_ascii_false() -> bool {
    let a: [u8; 3] = [65, 128, 67];
    a.as_slice().is_ascii() == false
}

#[rust_lean_test]
pub fn test_is_ascii_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().is_ascii()
}

#[rust_lean_test]
pub fn test_eq_ignore_ascii_case_true() -> bool {
    let a: [u8; 3] = [b'A', b'b', b'C'];
    let b: [u8; 3] = [b'a', b'B', b'c'];
    a.as_slice().eq_ignore_ascii_case(b.as_slice())
}

#[rust_lean_test]
pub fn test_eq_ignore_ascii_case_false() -> bool {
    let a: [u8; 3] = [b'A', b'b', b'C'];
    let b: [u8; 3] = [b'a', b'B', b'd'];
    a.as_slice().eq_ignore_ascii_case(b.as_slice()) == false
}

#[rust_lean_test]
pub fn test_eq_ignore_ascii_case_len_mismatch() -> bool {
    let a: [u8; 2] = [b'a', b'b'];
    let b: [u8; 3] = [b'a', b'b', b'c'];
    a.as_slice().eq_ignore_ascii_case(b.as_slice()) == false
}

#[rust_lean_test]
pub fn test_trim_ascii_start() -> bool {
    let a: [u8; 5] = [b' ', b'\t', b'x', b'y', b' '];
    let e: &[u8] = &[b'x', b'y', b' '];
    a.as_slice().trim_ascii_start() == e
}

#[rust_lean_test]
pub fn test_trim_ascii_end() -> bool {
    let a: [u8; 5] = [b' ', b'\t', b'x', b'y', b' '];
    let e: &[u8] = &[b' ', b'\t', b'x', b'y'];
    a.as_slice().trim_ascii_end() == e
}

#[rust_lean_test]
pub fn test_trim_ascii_both() -> bool {
    let a: [u8; 5] = [b' ', b'\t', b'x', b'y', b' '];
    let e: &[u8] = &[b'x', b'y'];
    a.as_slice().trim_ascii() == e
}

#[rust_lean_test]
pub fn test_trim_ascii_all_whitespace() -> bool {
    let a: [u8; 3] = [b' ', b' ', b' '];
    a.as_slice().trim_ascii().is_empty()
}

#[rust_lean_test]
pub fn test_trim_ascii_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().trim_ascii().is_empty()
}

#[rust_lean_test]
pub fn test_make_ascii_uppercase() -> bool {
    let mut a = [b'a', b'B', b'!'];
    let s: &mut [u8] = &mut a;
    s.make_ascii_uppercase();
    a == [b'A', b'B', b'!']
}

#[rust_lean_test]
pub fn test_make_ascii_lowercase() -> bool {
    let mut a = [b'a', b'B', b'!'];
    let s: &mut [u8] = &mut a;
    s.make_ascii_lowercase();
    a == [b'a', b'b', b'!']
}

// ----------------------------------------------------------------------------
// Predicate-driven items (`split`, `splitn`, `rsplit`, `rsplitn`,
// `split_inclusive`, `chunk_by`, `split_once`, `rsplit_once`,
// `binary_search_by`, `binary_search_by_key`, `partition_point`,
// `is_sorted_by`, `is_sorted_by_key`, `fill_with`) all take a closure at the
// call site, which the Lean extraction does not handle. They are covered by the
// proptests in `core-models/src/core/slice.rs`; the Rust-only tests below pin
// the same observations here.
// TODO(closure-extraction): turn these into `#[rust_lean_test]`s.
// ----------------------------------------------------------------------------

#[cfg(test)]
#[test]
fn test_split_on_zero() {
    let a: [u8; 6] = [1, 0, 2, 3, 0, 4];
    let got: Vec<&[u8]> = a.as_slice().split(|x| *x == 0).collect();
    assert_eq!(got, vec![&[1u8][..], &[2u8, 3][..], &[4u8][..]]);
}

#[cfg(test)]
#[test]
fn test_split_inclusive_on_zero() {
    let a: [u8; 4] = [1, 0, 2, 0];
    let got: Vec<&[u8]> = a.as_slice().split_inclusive(|x| *x == 0).collect();
    assert_eq!(got, vec![&[1u8, 0][..], &[2u8, 0][..]]);
}

#[cfg(test)]
#[test]
fn test_splitn_limits() {
    let a: [u8; 5] = [1, 0, 2, 0, 3];
    let got: Vec<&[u8]> = a.as_slice().splitn(2, |x| *x == 0).collect();
    assert_eq!(got, vec![&[1u8][..], &[2u8, 0, 3][..]]);
}

#[cfg(test)]
#[test]
fn test_rsplit_reverses() {
    let a: [u8; 5] = [1, 0, 2, 0, 3];
    let got: Vec<&[u8]> = a.as_slice().rsplit(|x| *x == 0).collect();
    assert_eq!(got, vec![&[3u8][..], &[2u8][..], &[1u8][..]]);
}

#[cfg(test)]
#[test]
fn test_rsplitn_limits() {
    let a: [u8; 5] = [1, 0, 2, 0, 3];
    let got: Vec<&[u8]> = a.as_slice().rsplitn(2, |x| *x == 0).collect();
    assert_eq!(got, vec![&[3u8][..], &[1u8, 0, 2][..]]);
}

#[cfg(test)]
#[test]
fn test_chunk_by_runs() {
    let a: [u8; 6] = [1, 2, 3, 1, 2, 1];
    let got: Vec<&[u8]> = a.as_slice().chunk_by(|x, y| x <= y).collect();
    assert_eq!(got, vec![&[1u8, 2, 3][..], &[1u8, 2][..], &[1u8][..]]);
}

#[cfg(test)]
#[test]
fn test_split_once_and_rsplit_once() {
    let a: [u8; 5] = [1, 0, 2, 0, 3];
    assert_eq!(
        a.as_slice().split_once(|x| *x == 0),
        Some((&[1u8][..], &[2u8, 0, 3][..]))
    );
    assert_eq!(
        a.as_slice().rsplit_once(|x| *x == 0),
        Some((&[1u8, 0, 2][..], &[3u8][..]))
    );
    let b: [u8; 2] = [1, 2];
    assert_eq!(b.as_slice().split_once(|x| *x == 0), None);
}

#[cfg(test)]
#[test]
fn test_binary_search_by_and_key() {
    let a: [u8; 4] = [1, 3, 5, 7];
    assert_eq!(a.as_slice().binary_search_by(|p| p.cmp(&5)), Ok(2));
    assert_eq!(a.as_slice().binary_search_by(|p| p.cmp(&4)), Err(2));
    assert_eq!(a.as_slice().binary_search_by_key(&7, |p| *p), Ok(3));
    let e: [u8; 0] = [];
    assert_eq!(e.as_slice().binary_search_by(|p| p.cmp(&1)), Err(0));
}

#[cfg(test)]
#[test]
fn test_partition_point_boundaries() {
    let a: [u8; 5] = [1, 2, 3, 4, 5];
    assert_eq!(a.as_slice().partition_point(|x| *x < 1), 0);
    assert_eq!(a.as_slice().partition_point(|x| *x < 3), 2);
    assert_eq!(a.as_slice().partition_point(|x| *x < 9), 5);
    let e: [u8; 0] = [];
    assert_eq!(e.as_slice().partition_point(|x| *x < 3), 0);
}

#[cfg(test)]
#[test]
fn test_is_sorted_by_and_key() {
    let a: [u8; 3] = [1, 2, 2];
    assert!(a.as_slice().is_sorted_by(|x, y| x <= y));
    assert!(!a.as_slice().is_sorted_by(|x, y| x < y));
    assert!(a.as_slice().is_sorted_by_key(|x| *x));
}

#[cfg(test)]
#[test]
fn test_fill_with() {
    let mut a: [u8; 3] = [0, 0, 0];
    let s: &mut [u8] = &mut a;
    s.fill_with(|| 7);
    assert_eq!(a, [7, 7, 7]);
}
