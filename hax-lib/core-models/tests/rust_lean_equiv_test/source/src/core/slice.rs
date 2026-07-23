//! Equivalence tests for `[T]` (`core::slice`) operations.
//!
//! These mirror the proptest block in `core-models/src/core/slice.rs`.

use rust_lean_test_macro::rust_lean_test;

// ----- len -------------------------------------------------------------------

// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_len_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().len() == 0
}
*/

// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_len_one() -> bool {
    let a: [u8; 1] = [42];
    a.as_slice().len() == 1
}
*/

// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_len_eight() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a.as_slice().len() == 8
}
*/

// ----- is_empty --------------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_is_empty_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().is_empty()
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_is_empty_one() -> bool {
    let a: [u8; 1] = [0];
    a.as_slice().is_empty() == false
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_is_empty_many() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().is_empty() == false
}
*/
*/
*/

// ----- contains --------------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_contains_present() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&3)
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_contains_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&1)
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_contains_absent() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().contains(&99) == false
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::contains` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_contains_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().contains(&0) == false
}
*/
*/
*/

// ----- split_at --------------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_zero() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(0);
    l.is_empty() && r.len() == 4
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::is_empty` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_full() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(4);
    l.len() == 4 && r.is_empty()
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_middle_lens() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, r) = a.as_slice().split_at(2);
    l.len() == 2 && r.len() == 2
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_middle_left_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (l, _r) = a.as_slice().split_at(2);
    l[0] == 1
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_middle_right_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let (_l, r) = a.as_slice().split_at(2);
    r[0] == 3
}
*/
*/
*/

// ----- split_at_checked ------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_checked_in_range_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(2).is_some()
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_checked_at_end_some() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(4).is_some()
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::split_at_checked` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_split_at_checked_out_of_range_none() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.as_slice().split_at_checked(5).is_none()
}
*/
*/
*/

// ----- first -----------------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_first_present() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().first() {
        Some(v) => *v == 10,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_first_some_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().first() {
        Some(v) => *v == 7,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::first` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_first_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().first().is_none()
}
*/
*/
*/

// ----- last ------------------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_last_present() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().last() {
        Some(v) => *v == 40,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_last_some_one() -> bool {
    let a: [u8; 1] = [7];
    match a.as_slice().last() {
        Some(v) => *v == 7,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::last` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_last_empty_none() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().last().is_none()
}
*/
*/
*/

// ----- get (usize) -----------------------------------------------------------

// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_get_usize_in_range() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().get(2) {
        Some(v) => *v == 30,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_get_usize_first() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    match a.as_slice().get(0) {
        Some(v) => *v == 10,
        None => false,
    }
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_get_usize_out_of_range() -> bool {
    let a: [u8; 4] = [10, 20, 30, 40];
    a.as_slice().get(4).is_none()
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(slice-method-missing: `<[T]>::get` returns `Option<&T>` whose reference shape doesn't survive extraction.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_get_usize_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().get(0).is_none()
}
*/
*/
*/

// ----- starts_with / ends_with ----------------------------------------------

// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_starts_with_true() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [1, 2];
    a.as_slice().starts_with(needle.as_slice())
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_starts_with_empty_needle() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 0] = [];
    a.as_slice().starts_with(needle.as_slice())
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::starts_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_starts_with_false() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [2, 3];
    a.as_slice().starts_with(needle.as_slice()) == false
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_ends_with_true() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [3, 4];
    a.as_slice().ends_with(needle.as_slice())
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_ends_with_empty_needle() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 0] = [];
    a.as_slice().ends_with(needle.as_slice())
}
*/
*/
*/

// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(slice-method-missing: `<[T]>::ends_with` not in extracted Lean.)
/*
// TODO(array-as_slice-extraction: `<[T; N]>::as_slice` extracts to a `core_models.array.Array.as_slice` def the Lean library does not define.)
/*
#[rust_lean_test]
pub fn test_ends_with_false() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let needle: [u8; 2] = [2, 3];
    a.as_slice().ends_with(needle.as_slice()) == false
}
*/
*/
*/

// ----- skipped methods -------------------------------------------------------

// TODO(slice-index-excluded): SliceIndex impls are in CHARON_EXCLUDES; revisit
// when SliceIndex modelling lands. The following tests would exercise
// `slice[range]`, `slice.get(range)`, `slice[range_from]`, etc.
// pub fn test_index_range() -> bool {
//     let a: [u8; 4] = [1, 2, 3, 4];
//     a.as_slice()[1..3] == [2, 3]
// }
// pub fn test_get_range_some() -> bool {
//     let a: [u8; 4] = [1, 2, 3, 4];
//     a.as_slice().get(1..3).is_some()
// }
// pub fn test_index_range_to() -> bool {
//     let a: [u8; 4] = [1, 2, 3, 4];
//     a.as_slice()[..2] == [1, 2]
// }
// pub fn test_index_range_from() -> bool {
//     let a: [u8; 4] = [1, 2, 3, 4];
//     a.as_slice()[2..] == [3, 4]
// }
// pub fn test_index_range_full() -> bool {
//     let a: [u8; 4] = [1, 2, 3, 4];
//     a.as_slice()[..] == [1, 2, 3, 4]
// }

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

// TODO(mut-slice-extraction): `copy_from_slice`, `clone_from_slice`, `fill` take
// `&mut [T]` and remain opaque; revisit later.
// pub fn test_fill() -> bool {
//     let mut a: [u8; 4] = [0, 0, 0, 0];
//     a.as_mut_slice().fill(7);
//     a == [7, 7, 7, 7]
// }

// TODO(slice-iter-extraction): `iter()`, `chunks()`, `chunks_exact()`,
// `windows()` produce iterators whose `next` consumes `&mut Self`; this
// pattern is awkward to drive from a pure `() -> bool` test without
// `&mut` plumbing the Lean side may not handle yet. Revisit.
// pub fn test_iter_count() -> bool {
//     let a: [u8; 3] = [1, 2, 3];
//     a.as_slice().iter().count() == 3
// }

// TODO(opaque-binary-search): `binary_search` is opaque (`#[hax_lib::opaque]`)
// in the model; equivalence would only check signature, not value.
// pub fn test_binary_search() -> bool { ... }

// TODO(opaque-copy-within): `copy_within` is opaque in the model.
// pub fn test_copy_within() -> bool { ... }

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

// TODO(slice-index-range-extraction: indexing a slice via `RangeTo`/`RangeFull` hits an excluded path; manual def doesn't yet cover the Range* variants.)
/*
#[rust_lean_test]
pub fn test_slice_index_range_to_len() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t.len() == 3
}
*/

// TODO(slice-index-range-extraction: indexing a slice via `RangeTo`/`RangeFull` hits an excluded path; manual def doesn't yet cover the Range* variants.)
/*
#[rust_lean_test]
pub fn test_slice_index_range_to_first_elem() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t[0] == 10
}
*/

// TODO(slice-index-range-extraction: indexing a slice via `RangeTo`/`RangeFull` hits an excluded path; manual def doesn't yet cover the Range* variants.)
/*
#[rust_lean_test]
pub fn test_slice_index_range_to_last_elem() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..3];
    t[2] == 30
}
*/

// ----- &s[..] : RangeFull (manually defined in Lean, not extracted) ---------

// TODO(slice-index-range-extraction: indexing a slice via `RangeTo`/`RangeFull` hits an excluded path; manual def doesn't yet cover the Range* variants.)
/*
#[rust_lean_test]
pub fn test_slice_index_range_full_len() -> bool {
    let s: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let t: &[u8] = &s[..];
    t.len() == 8
}
*/

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
