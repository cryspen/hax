//! Equivalence tests for `alloc::vec::Vec::*`.
//!
//! Mirrors the proptest cases in `alloc/src/lib.rs` (module `vec::tests`),
//! pinning each observation on a concrete input.
//!
//! Notes on what's tested:
//! - Indexing `v[i]` is in `ALLOC_CHARON_EXCLUDES` (see top-level `Makefile`),
//!   so we verify per-element contents by sequential `pop()`s instead of
//!   `v[i] == x`.

use rust_lean_test_macro::rust_lean_test;

// ----- new -------------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_new_len_zero() -> bool {
    let v: Vec<u8> = Vec::new();
    v.len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_new_is_empty() -> bool {
    let v: Vec<u8> = Vec::new();
    v.is_empty()
}
*/

// ----- with_capacity ---------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_with_capacity_zero_len() -> bool {
    let v: Vec<u8> = Vec::with_capacity(0);
    v.len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_with_capacity_ten_len() -> bool {
    let v: Vec<u8> = Vec::with_capacity(10);
    v.len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_with_capacity_is_empty() -> bool {
    let v: Vec<u8> = Vec::with_capacity(100);
    v.is_empty()
}
*/

// ----- len -------------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_len_empty() -> bool {
    let v: Vec<u8> = Vec::new();
    v.len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_len_one() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(42);
    v.len() == 1
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_len_from_elem() -> bool {
    let v: Vec<u8> = vec![3u8; 5];
    v.len() == 5
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_len_from_elem_zero() -> bool {
    let v: Vec<u8> = vec![0u8; 0];
    v.len() == 0
}
*/

// ----- is_empty --------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_is_empty_new() -> bool {
    let v: Vec<u8> = Vec::new();
    v.is_empty() == true
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_is_empty_after_push() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.is_empty() == false
}
*/

// ----- as_slice --------------------------------------------------------------
//
// `as_slice` returns `&[T]`. We can observe it through length-via-deref
// (Vec implements Deref<Target=[T]>) but `len` on a slice is the same
// as `Vec::len`, so we mostly exercise that `as_slice` is well-typed.

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_as_slice_empty_len() -> bool {
    let v: Vec<u8> = Vec::new();
    v.as_slice().len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_as_slice_one_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(9);
    v.as_slice().len() == 1
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_as_slice_three_len() -> bool {
    let v: Vec<u8> = vec![4u8; 3];
    v.as_slice().len() == 3
}
*/

// ----- push ------------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_push_one_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.len() == 1
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_push_many_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.len() == 3
}
*/

// ----- append ----------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_append_both_empty() -> bool {
    let mut a: Vec<u8> = Vec::new();
    let mut b: Vec<u8> = Vec::new();
    a.append(&mut b);
    a.len() == 0 && b.len() == 0
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_append_empty_to_nonempty() -> bool {
    let mut a: Vec<u8> = Vec::new();
    a.push(1);
    a.push(2);
    let mut b: Vec<u8> = Vec::new();
    a.append(&mut b);
    a.len() == 2 && b.len() == 0
}
*/

// ----- extend_from_slice -----------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_extend_from_slice_empty_to_empty() -> bool {
    let mut v: Vec<u8> = Vec::new();
    let s: [u8; 0] = [];
    v.extend_from_slice(&s);
    v.len() == 0
}
*/

// ----- from_elem (`vec![x; n]`) ---------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_from_elem_zero_len() -> bool {
    let v: Vec<u8> = vec![9u8; 0];
    v.len() == 0 && v.is_empty()
}
*/

// ----- index (excluded) ------------------------------------------------------

// TODO(vec-index-excluded): Vec<T>::index is in ALLOC_CHARON_EXCLUDES.
// pub fn test_vec_index_first() -> bool {
//     let v: Vec<u8> = vec![7u8; 1];
//     v[0] == 7
// }

// TODO(vec-index-excluded): Vec<T>::index is in ALLOC_CHARON_EXCLUDES.
// pub fn test_vec_index_range() -> bool {
//     let v: Vec<u8> = vec![7u8; 3];
//     v[0..2].len() == 2
// }

// ----- sort_by (excluded) ----------------------------------------------------

// TODO(vec-index-excluded): Vec::sort_by is in ALLOC_CHARON_EXCLUDES (closure
// extraction is unsupported).

// ----- from_iter (excluded) --------------------------------------------------

// TODO(vec-index-excluded): Vec::from_iter is in ALLOC_CHARON_EXCLUDES.

// ----- remove ----------------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)

/* #[rust_lean_test]
pub fn test_vec_remove_only_element() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    let x = v.remove(0);
    x == 7 && v.is_empty()
} */

// ----- swap_remove -----------------------------------------------------------

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_swap_remove_only_element() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(9);
    let x = v.swap_remove(0);
    x == 9 && v.is_empty()
}
*/

// TODO(vec-extraction-arity-mismatch: the Lean model marks `Vec.is_empty`/`as_slice`/`pop`/... with implicit `{A}`, but Aeneas extracts the call applying the allocator explicitly. Until that mismatch is fixed in the model, `Vec::*` tests fail.)
/*
#[rust_lean_test]
pub fn test_vec_swap_remove_back() -> bool {
    // Swap-removing the last element behaves like `pop` (modulo the
    // option). Our model body is `seq_remove(self, n)`, which is the same
    // ordered removal — so we observe it as a plain remove.
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let x = v.swap_remove(2);
    x == 3 && v.len() == 2
}
*/

// ----- truncate / resize / clear (stubbed in Lean) ---------------------------

// TODO(opaque-in-model): Vec::truncate is `#[hax_lib::opaque]` in the model
// and the extracted Lean body is `ok self` (no-op), so a comparison
// against std's truncate cannot hold on the Lean side.
// TODO(opaque-in-model): Vec::resize is `#[hax_lib::opaque]` in the model
// and the extracted Lean body is `ok self`.
// TODO(opaque-in-model): Vec::clear is `#[hax_lib::opaque]` in the model
// and the extracted Lean body is `ok self`.

// ----- drain (iterator) ------------------------------------------------------

// TODO(vec-iter-extraction): Vec::drain returns an iterator we don't have
// a stable way to drive in extracted Lean yet.

// ----- closure-using methods (excluded) --------------------------------------

// TODO(closure-extraction + vec-extraction-arity-mismatch): Vec::retain takes
// a closure. Aeneas can extract the closure (see core::array::from_fn) but
// every Vec method first trips on the arity-mismatch issue above. Revisit
// once Vec tests can compile in the first place.
// TODO(vec-iter-extraction): Vec::iter / Vec::into_iter use iterator traits
// whose Lean models we don't have yet.

#[rust_lean_test]
pub fn test_vec_new_len_zero() -> bool {
    let v: Vec<u8> = Vec::new();
    v.len() == 0
}

#[rust_lean_test]
pub fn test_vec_push_len() -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(7u8);
    v.len() == 1
}

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
