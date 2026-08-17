//! Equivalence tests for `alloc::collections::*`.
//!
//! Mirrors the proptest cases in `alloc/src/lib.rs` (module
//! `collections::vec_deque::tests`), pinning each observation on a concrete
//! input.
//!
//! Notes on what is *not* here:
//! - `VecDeque::{new_in, with_capacity_in, try_with_capacity, truncate_front}`
//!   and `TryReserveError::kind` are unstable in std, so a stable client cannot
//!   call them; their behaviour is pinned by the model crate's own tests.
//! - The closure-taking methods (`retain`, `resize_with`, `binary_search_by`,
//!   `binary_search_by_key`, `partition_point`) and `iter` are commented out
//!   below — see the TODOs.

use rust_lean_test_macro::rust_lean_test;
use std::collections::VecDeque;

// ----- new / with_capacity ---------------------------------------------------

#[rust_lean_test]
pub fn test_deque_new_len_zero() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    d.len() == 0
}

#[rust_lean_test]
pub fn test_deque_new_is_empty() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    d.is_empty()
}

#[rust_lean_test]
pub fn test_deque_with_capacity_is_empty() -> bool {
    let d: VecDeque<u8> = VecDeque::with_capacity(10);
    d.is_empty() && d.len() == 0
}

// ----- push_back / push_front ------------------------------------------------

#[rust_lean_test]
pub fn test_deque_push_back_len() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.len() == 2 && d.is_empty() == false
}

#[rust_lean_test]
pub fn test_deque_push_front_order() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(2);
    d.push_front(1);
    d.len() == 2 && d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_push_front_into_empty() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_front(u8::MAX);
    d.len() == 1 && d[0] == u8::MAX
}

// ----- pop_front / pop_back --------------------------------------------------

#[rust_lean_test]
pub fn test_deque_pop_front_empty_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.pop_front().is_none()
}

#[rust_lean_test]
pub fn test_deque_pop_back_empty_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.pop_back().is_none()
}

#[rust_lean_test]
pub fn test_deque_pop_front_takes_first() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.pop_front().unwrap_or(0) == 1 && d.len() == 1
}

#[rust_lean_test]
pub fn test_deque_pop_back_takes_last() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.pop_back().unwrap_or(0) == 2 && d.len() == 1
}

#[rust_lean_test]
pub fn test_deque_pop_back_single() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(7);
    d.pop_back().unwrap_or(0) == 7 && d.is_empty()
}

// ----- get -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_get_empty_is_none() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    d.get(0).is_none()
}

#[rust_lean_test]
pub fn test_deque_get_in_bounds() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(5);
    d.push_back(6);
    match d.get(1) {
        Some(x) => *x == 6,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_deque_get_past_end_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(5);
    d.get(1).is_none()
}

// ----- front / back ----------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_front_back_empty_are_none() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    d.front().is_none() && d.back().is_none()
}

#[rust_lean_test]
pub fn test_deque_front_back_single_coincide() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(4);
    match d.front() {
        Some(f) => match d.back() {
            Some(b) => *f == 4 && *b == 4,
            None => false,
        },
        None => false,
    }
}

#[rust_lean_test]
pub fn test_deque_front_back_three() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    match d.front() {
        Some(f) => match d.back() {
            Some(b) => *f == 1 && *b == 3,
            None => false,
        },
        None => false,
    }
}

// ----- swap ------------------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_swap_same_index_is_identity() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.swap(1, 1);
    d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_swap_ends() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.swap(0, 2);
    d[0] == 3 && d[1] == 2 && d[2] == 1
}

#[rust_lean_test]
pub fn test_deque_swap_high_then_low() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.swap(2, 1);
    d[0] == 1 && d[1] == 3 && d[2] == 2
}

// ----- insert / remove -------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_insert_at_front() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(2);
    d.insert(0, 1);
    d.len() == 2 && d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_insert_at_end() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.insert(1, 2);
    d.len() == 2 && d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_insert_into_empty() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.insert(0, 9);
    d.len() == 1 && d[0] == 9
}

#[rust_lean_test]
pub fn test_deque_remove_empty_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.remove(0).is_none()
}

#[rust_lean_test]
pub fn test_deque_remove_middle() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.remove(1).unwrap_or(0) == 2 && d.len() == 2 && d[0] == 1 && d[1] == 3
}

#[rust_lean_test]
pub fn test_deque_remove_past_end_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.remove(1).is_none() && d.len() == 1
}

// ----- swap_remove_front / swap_remove_back ----------------------------------

#[rust_lean_test]
pub fn test_deque_swap_remove_front_empty_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.swap_remove_front(0).is_none()
}

#[rust_lean_test]
pub fn test_deque_swap_remove_front_moves_head() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    // Removes index 2, and the old head lands where it was.
    d.swap_remove_front(2).unwrap_or(0) == 3 && d.len() == 2 && d[0] == 2 && d[1] == 1
}

#[rust_lean_test]
pub fn test_deque_swap_remove_back_empty_is_none() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.swap_remove_back(0).is_none()
}

#[rust_lean_test]
pub fn test_deque_swap_remove_back_moves_tail() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.swap_remove_back(0).unwrap_or(0) == 1 && d.len() == 2 && d[0] == 3 && d[1] == 2
}

// ----- clear / truncate ------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_clear_empties() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.clear();
    d.is_empty() && d.len() == 0
}

#[rust_lean_test]
pub fn test_deque_clear_on_empty() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.clear();
    d.is_empty()
}

#[rust_lean_test]
pub fn test_deque_truncate_shortens() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.truncate(1);
    d.len() == 1 && d[0] == 1
}

#[rust_lean_test]
pub fn test_deque_truncate_to_zero() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.truncate(0);
    d.is_empty()
}

#[rust_lean_test]
pub fn test_deque_truncate_past_end_is_noop() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.truncate(5);
    d.len() == 1 && d[0] == 1
}

// ----- split_off / append ----------------------------------------------------

#[rust_lean_test]
pub fn test_deque_split_off_at_zero() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    let t = d.split_off(0);
    d.is_empty() && t.len() == 2 && t[0] == 1 && t[1] == 2
}

#[rust_lean_test]
pub fn test_deque_split_off_at_len() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    let t = d.split_off(1);
    d.len() == 1 && t.is_empty()
}

#[rust_lean_test]
pub fn test_deque_split_off_middle() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    let t = d.split_off(1);
    d.len() == 1 && d[0] == 1 && t.len() == 2 && t[0] == 2 && t[1] == 3
}

#[rust_lean_test]
pub fn test_deque_append_both_empty() -> bool {
    let mut a: VecDeque<u8> = VecDeque::new();
    let mut b: VecDeque<u8> = VecDeque::new();
    a.append(&mut b);
    a.is_empty() && b.is_empty()
}

#[rust_lean_test]
pub fn test_deque_append_drains_other() -> bool {
    let mut a: VecDeque<u8> = VecDeque::new();
    a.push_back(1);
    let mut b: VecDeque<u8> = VecDeque::new();
    b.push_back(2);
    a.append(&mut b);
    a.len() == 2 && a[0] == 1 && a[1] == 2 && b.is_empty()
}

// ----- rotate_left / rotate_right --------------------------------------------

#[rust_lean_test]
pub fn test_deque_rotate_left_zero_is_identity() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.rotate_left(0);
    d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_rotate_left_one() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.rotate_left(1);
    d[0] == 2 && d[1] == 3 && d[2] == 1
}

#[rust_lean_test]
pub fn test_deque_rotate_left_full_is_identity() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.rotate_left(2);
    d[0] == 1 && d[1] == 2
}

#[rust_lean_test]
pub fn test_deque_rotate_right_one() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.push_back(3);
    d.rotate_right(1);
    d[0] == 3 && d[1] == 1 && d[2] == 2
}

#[rust_lean_test]
pub fn test_deque_rotate_on_empty_is_identity() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.rotate_left(0);
    d.rotate_right(0);
    d.is_empty()
}

// ----- contains --------------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_contains_empty_is_false() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    d.contains(&0) == false
}

#[rust_lean_test]
pub fn test_deque_contains_present() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.contains(&2)
}

#[rust_lean_test]
pub fn test_deque_contains_absent() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.contains(&u8::MAX) == false
}

// ----- as_slices -------------------------------------------------------------
//
// The model is always contiguous, so its back slice is always empty; std may
// split. Only the total length is a shared observation.

#[rust_lean_test]
pub fn test_deque_as_slices_total_len() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    let parts = d.as_slices();
    parts.0.len() + parts.1.len() == 2
}

#[rust_lean_test]
pub fn test_deque_as_slices_empty() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    let parts = d.as_slices();
    parts.0.len() + parts.1.len() == 0
}

// ----- reserve / shrink / try_reserve ----------------------------------------

#[rust_lean_test]
pub fn test_deque_reserve_preserves_contents() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.reserve(100);
    d.reserve_exact(100);
    d.len() == 1 && d[0] == 1
}

#[rust_lean_test]
pub fn test_deque_shrink_preserves_contents() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.shrink_to(0);
    d.shrink_to_fit();
    d.len() == 1 && d[0] == 1
}

#[rust_lean_test]
pub fn test_deque_try_reserve_is_ok() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    match d.try_reserve(4) {
        Ok(()) => true,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_deque_try_reserve_exact_is_ok() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    match d.try_reserve_exact(4) {
        Ok(()) => true,
        Err(_) => false,
    }
}

// ----- resize ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_resize_grows() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.resize(3, 7);
    d.len() == 3 && d[0] == 1 && d[1] == 7 && d[2] == 7
}

#[rust_lean_test]
pub fn test_deque_resize_shrinks() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(2);
    d.resize(1, 0);
    d.len() == 1 && d[0] == 1
}

#[rust_lean_test]
pub fn test_deque_resize_to_zero() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.resize(0, 0);
    d.is_empty()
}

// ----- binary_search ---------------------------------------------------------

#[rust_lean_test]
pub fn test_deque_binary_search_found() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(3);
    d.push_back(5);
    match d.binary_search(&3) {
        Ok(i) => i == 1,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_deque_binary_search_insertion_point() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    d.push_back(5);
    match d.binary_search(&3) {
        Ok(_) => false,
        Err(i) => i == 1,
    }
}

#[rust_lean_test]
pub fn test_deque_binary_search_empty() -> bool {
    let d: VecDeque<u8> = VecDeque::new();
    match d.binary_search(&0) {
        Ok(_) => false,
        Err(i) => i == 0,
    }
}

#[rust_lean_test]
pub fn test_deque_binary_search_past_end() -> bool {
    let mut d: VecDeque<u8> = VecDeque::new();
    d.push_back(1);
    match d.binary_search(&u8::MAX) {
        Ok(_) => false,
        Err(i) => i == 1,
    }
}

// ----- closure-taking methods ------------------------------------------------

// TODO(closure-extraction): `VecDeque::{retain, resize_with, binary_search_by,
// binary_search_by_key, partition_point}` take a closure at the *client* call
// site, which extracts poorly. Their behaviour is covered by the proptests in
// `alloc/src/lib.rs`.

// ----- iter ------------------------------------------------------------------

// TODO(iterator-extraction): `VecDeque::iter` returns an `Iterator`, and the
// equivalence framework has no `Iterator`-consuming test yet (the `core::iter`
// cases are plain `#[test]`s for the same reason).

// ----- TryReserveError -------------------------------------------------------

// `TryReserveError` has no stable constructor and `kind` is unstable
// (`try_reserve_kind`), so there is nothing a stable client can observe beyond
// `try_reserve` returning `Ok` (above).
