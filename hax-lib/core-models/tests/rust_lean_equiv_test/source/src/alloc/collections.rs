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
use std::collections::{BTreeMap, BTreeSet, LinkedList, VecDeque};

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

// =============================================================================
// LinkedList
// =============================================================================
//
// `LinkedList::{new_in, remove, retain}` are unstable in std, so they are only
// covered by the model crate's own tests. `LinkedList` has no `Index` impl, so
// contents are observed by popping.

// ----- new -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_list_new_is_empty() -> bool {
    let l: LinkedList<u8> = LinkedList::new();
    l.is_empty() && l.len() == 0
}

// ----- push_back / push_front / len ------------------------------------------

#[rust_lean_test]
pub fn test_list_push_back_len() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.len() == 2 && l.is_empty() == false
}

#[rust_lean_test]
pub fn test_list_push_front_order() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(2);
    l.push_front(1);
    l.pop_front().unwrap_or(0) == 1 && l.pop_front().unwrap_or(0) == 2 && l.is_empty()
}

#[rust_lean_test]
pub fn test_list_push_front_into_empty() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_front(u8::MAX);
    l.len() == 1 && l.pop_back().unwrap_or(0) == u8::MAX
}

// ----- pop_front / pop_back --------------------------------------------------

#[rust_lean_test]
pub fn test_list_pop_front_empty_is_none() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.pop_front().is_none()
}

#[rust_lean_test]
pub fn test_list_pop_back_empty_is_none() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.pop_back().is_none()
}

#[rust_lean_test]
pub fn test_list_pop_back_takes_last() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.pop_back().unwrap_or(0) == 2 && l.len() == 1
}

// ----- front / back ----------------------------------------------------------

#[rust_lean_test]
pub fn test_list_front_back_empty_are_none() -> bool {
    let l: LinkedList<u8> = LinkedList::new();
    l.front().is_none() && l.back().is_none()
}

#[rust_lean_test]
pub fn test_list_front_back_single_coincide() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(4);
    match l.front() {
        Some(f) => match l.back() {
            Some(b) => *f == 4 && *b == 4,
            None => false,
        },
        None => false,
    }
}

#[rust_lean_test]
pub fn test_list_front_back_three() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);
    match l.front() {
        Some(f) => match l.back() {
            Some(b) => *f == 1 && *b == 3,
            None => false,
        },
        None => false,
    }
}

// ----- clear -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_list_clear_empties() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.clear();
    l.is_empty() && l.len() == 0
}

#[rust_lean_test]
pub fn test_list_clear_on_empty() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.clear();
    l.is_empty()
}

// ----- contains --------------------------------------------------------------

#[rust_lean_test]
pub fn test_list_contains_empty_is_false() -> bool {
    let l: LinkedList<u8> = LinkedList::new();
    l.contains(&0) == false
}

#[rust_lean_test]
pub fn test_list_contains_present() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.contains(&2)
}

#[rust_lean_test]
pub fn test_list_contains_absent() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.contains(&u8::MAX) == false
}

// ----- append ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_list_append_both_empty() -> bool {
    let mut a: LinkedList<u8> = LinkedList::new();
    let mut b: LinkedList<u8> = LinkedList::new();
    a.append(&mut b);
    a.is_empty() && b.is_empty()
}

#[rust_lean_test]
pub fn test_list_append_drains_other() -> bool {
    let mut a: LinkedList<u8> = LinkedList::new();
    a.push_back(1);
    let mut b: LinkedList<u8> = LinkedList::new();
    b.push_back(2);
    a.append(&mut b);
    a.len() == 2 && b.is_empty() && a.pop_back().unwrap_or(0) == 2
}

// ----- split_off -------------------------------------------------------------

#[rust_lean_test]
pub fn test_list_split_off_at_zero() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    let mut t = l.split_off(0);
    l.is_empty() && t.len() == 2 && t.pop_front().unwrap_or(0) == 1
}

#[rust_lean_test]
pub fn test_list_split_off_at_len() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    let t = l.split_off(1);
    l.len() == 1 && t.is_empty()
}

#[rust_lean_test]
pub fn test_list_split_off_middle() -> bool {
    let mut l: LinkedList<u8> = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);
    let mut t = l.split_off(1);
    l.len() == 1
        && t.len() == 2
        && t.pop_front().unwrap_or(0) == 2
        && t.pop_front().unwrap_or(0) == 3
}

// ----- iter ------------------------------------------------------------------

// TODO(iterator-extraction): see the note on `VecDeque::iter` above.

// =============================================================================
// BTreeSet
// =============================================================================
//
// TODO(borrow-blanket-impl): `BTreeSet::{contains, get, remove, take,
// split_off}` are generic over a borrowed key (`T: Borrow<Q>`), and the model of
// `core::borrow::Borrow` has no blanket `impl<T> Borrow<T> for T`, so a client
// calling them at `Q = T` has no dictionary to pass. They are covered by the
// proptests in `alloc/src/lib.rs` instead.
//
// `BTreeSet::{iter, difference, intersection, union, symmetric_difference}`
// return iterators — see the `VecDeque::iter` note. `retain` takes a closure.
// `new_in` is unstable in std.

// ----- new -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_set_new_is_empty() -> bool {
    let s: BTreeSet<u8> = BTreeSet::new();
    s.is_empty() && s.len() == 0
}

// ----- insert / len ----------------------------------------------------------

#[rust_lean_test]
pub fn test_set_insert_new_is_true() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(3) && s.len() == 1
}

#[rust_lean_test]
pub fn test_set_insert_duplicate_is_false() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(3);
    s.insert(3) == false && s.len() == 1
}

#[rust_lean_test]
pub fn test_set_insert_sorts() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(3);
    s.insert(1);
    s.insert(2);
    s.len() == 3 && s.pop_first().unwrap_or(0) == 1 && s.pop_first().unwrap_or(0) == 2
}

#[rust_lean_test]
pub fn test_set_insert_boundaries() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(u8::MAX);
    s.insert(0);
    s.len() == 2 && s.pop_first().unwrap_or(1) == 0 && s.pop_last().unwrap_or(0) == u8::MAX
}

// ----- first / last ----------------------------------------------------------

#[rust_lean_test]
pub fn test_set_first_last_empty_are_none() -> bool {
    let s: BTreeSet<u8> = BTreeSet::new();
    s.first().is_none() && s.last().is_none()
}

#[rust_lean_test]
pub fn test_set_first_last_single_coincide() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(9);
    match s.first() {
        Some(f) => match s.last() {
            Some(l) => *f == 9 && *l == 9,
            None => false,
        },
        None => false,
    }
}

#[rust_lean_test]
pub fn test_set_first_last_three() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(2);
    s.insert(1);
    s.insert(3);
    match s.first() {
        Some(f) => match s.last() {
            Some(l) => *f == 1 && *l == 3,
            None => false,
        },
        None => false,
    }
}

// ----- pop_first / pop_last --------------------------------------------------

#[rust_lean_test]
pub fn test_set_pop_first_empty_is_none() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.pop_first().is_none()
}

#[rust_lean_test]
pub fn test_set_pop_last_empty_is_none() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.pop_last().is_none()
}

#[rust_lean_test]
pub fn test_set_pop_last_takes_greatest() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(1);
    s.insert(7);
    s.pop_last().unwrap_or(0) == 7 && s.len() == 1
}

// ----- replace ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_set_replace_absent_is_none() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.replace(4).is_none() && s.len() == 1
}

#[rust_lean_test]
pub fn test_set_replace_present_returns_old() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(4);
    s.replace(4).unwrap_or(0) == 4 && s.len() == 1
}

// ----- clear -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_set_clear_empties() -> bool {
    let mut s: BTreeSet<u8> = BTreeSet::new();
    s.insert(1);
    s.insert(2);
    s.clear();
    s.is_empty() && s.len() == 0
}

// ----- append ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_set_append_both_empty() -> bool {
    let mut a: BTreeSet<u8> = BTreeSet::new();
    let mut b: BTreeSet<u8> = BTreeSet::new();
    a.append(&mut b);
    a.is_empty() && b.is_empty()
}

#[rust_lean_test]
pub fn test_set_append_merges_and_dedups() -> bool {
    let mut a: BTreeSet<u8> = BTreeSet::new();
    a.insert(1);
    a.insert(2);
    let mut b: BTreeSet<u8> = BTreeSet::new();
    b.insert(2);
    b.insert(3);
    a.append(&mut b);
    a.len() == 3 && b.is_empty() && a.pop_last().unwrap_or(0) == 3
}

// ----- is_subset / is_superset / is_disjoint ---------------------------------

#[rust_lean_test]
pub fn test_set_empty_is_subset_of_everything() -> bool {
    let a: BTreeSet<u8> = BTreeSet::new();
    let mut b: BTreeSet<u8> = BTreeSet::new();
    b.insert(1);
    a.is_subset(&b) && b.is_superset(&a)
}

#[rust_lean_test]
pub fn test_set_is_subset_false() -> bool {
    let mut a: BTreeSet<u8> = BTreeSet::new();
    a.insert(1);
    a.insert(9);
    let mut b: BTreeSet<u8> = BTreeSet::new();
    b.insert(1);
    a.is_subset(&b) == false
}

#[rust_lean_test]
pub fn test_set_is_disjoint_true() -> bool {
    let mut a: BTreeSet<u8> = BTreeSet::new();
    a.insert(1);
    let mut b: BTreeSet<u8> = BTreeSet::new();
    b.insert(2);
    a.is_disjoint(&b)
}

#[rust_lean_test]
pub fn test_set_is_disjoint_false() -> bool {
    let mut a: BTreeSet<u8> = BTreeSet::new();
    a.insert(1);
    let mut b: BTreeSet<u8> = BTreeSet::new();
    b.insert(1);
    a.is_disjoint(&b) == false
}

#[rust_lean_test]
pub fn test_set_empty_sets_are_disjoint() -> bool {
    let a: BTreeSet<u8> = BTreeSet::new();
    let b: BTreeSet<u8> = BTreeSet::new();
    a.is_disjoint(&b) && a.is_subset(&b) && a.is_superset(&b)
}

// =============================================================================
// BTreeMap
// =============================================================================
//
// TODO(borrow-blanket-impl): `BTreeMap::{get, get_key_value, contains_key,
// remove, remove_entry, split_off}` are generic over a borrowed key, and the
// model of `core::borrow::Borrow` has no blanket `impl<T> Borrow<T> for T` — see
// the same note on `BTreeSet` above. Covered by the proptests instead.
//
// `BTreeMap::{iter, keys, values, into_keys, into_values}` return iterators —
// see the `VecDeque::iter` note. `new_in` is unstable in std.

// ----- new -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_map_new_is_empty() -> bool {
    let m: BTreeMap<u8, u8> = BTreeMap::new();
    m.is_empty() && m.len() == 0
}

// ----- insert / len ----------------------------------------------------------

#[rust_lean_test]
pub fn test_map_insert_new_returns_none() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(1, 10).is_none() && m.len() == 1
}

#[rust_lean_test]
pub fn test_map_insert_existing_returns_old() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(1, 20).unwrap_or(0) == 10 && m.len() == 1
}

#[rust_lean_test]
pub fn test_map_insert_sorts_by_key() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(3, 30);
    m.insert(1, 10);
    m.insert(2, 20);
    match m.pop_first() {
        Some(e) => e.0 == 1 && e.1 == 10 && m.len() == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_map_insert_key_boundaries() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(u8::MAX, 1);
    m.insert(0, 2);
    match m.pop_last() {
        Some(e) => e.0 == u8::MAX && e.1 == 1,
        None => false,
    }
}

// ----- first_key_value / last_key_value --------------------------------------

#[rust_lean_test]
pub fn test_map_first_last_empty_are_none() -> bool {
    let m: BTreeMap<u8, u8> = BTreeMap::new();
    m.first_key_value().is_none() && m.last_key_value().is_none()
}

#[rust_lean_test]
pub fn test_map_first_last_single_coincide() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(4, 40);
    match m.first_key_value() {
        Some(f) => match m.last_key_value() {
            Some(l) => *f.0 == 4 && *f.1 == 40 && *l.0 == 4 && *l.1 == 40,
            None => false,
        },
        None => false,
    }
}

#[rust_lean_test]
pub fn test_map_first_last_three() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(2, 20);
    m.insert(1, 10);
    m.insert(3, 30);
    match m.first_key_value() {
        Some(f) => match m.last_key_value() {
            Some(l) => *f.0 == 1 && *l.0 == 3,
            None => false,
        },
        None => false,
    }
}

// ----- pop_first / pop_last --------------------------------------------------

#[rust_lean_test]
pub fn test_map_pop_first_empty_is_none() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.pop_first().is_none()
}

#[rust_lean_test]
pub fn test_map_pop_last_empty_is_none() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.pop_last().is_none()
}

#[rust_lean_test]
pub fn test_map_pop_last_takes_greatest_key() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(7, 70);
    match m.pop_last() {
        Some(e) => e.0 == 7 && e.1 == 70 && m.len() == 1,
        None => false,
    }
}

// ----- clear -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_map_clear_empties() -> bool {
    let mut m: BTreeMap<u8, u8> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.clear();
    m.is_empty() && m.len() == 0
}

// ----- append ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_map_append_both_empty() -> bool {
    let mut a: BTreeMap<u8, u8> = BTreeMap::new();
    let mut b: BTreeMap<u8, u8> = BTreeMap::new();
    a.append(&mut b);
    a.is_empty() && b.is_empty()
}

// On a shared key the value from `other` wins.
#[rust_lean_test]
pub fn test_map_append_other_value_wins() -> bool {
    let mut a: BTreeMap<u8, u8> = BTreeMap::new();
    a.insert(1, 10);
    let mut b: BTreeMap<u8, u8> = BTreeMap::new();
    b.insert(1, 99);
    b.insert(2, 20);
    a.append(&mut b);
    a.len() == 2
        && b.is_empty()
        && match a.pop_first() {
            Some(e) => e.0 == 1 && e.1 == 99,
            None => false,
        }
}

// =============================================================================
// BinaryHeap (excluded from extraction, and *not* hand-written in Lean)
// =============================================================================
//
// TODO(binary-heap-no-lean): the whole `binary_heap` module is in
// `ALLOC_CHARON_EXCLUDES` (charon crashes on it), and unlike the other excluded
// items it has no hand-written counterpart under
// `hax-lib/proof-libs/lean/CoreModels/**`. A `#[rust_lean_test]` touching
// `BinaryHeap` would therefore reference an unknown constant and break the Lean
// build, so its behaviour is only covered by the proptests in
// `alloc/src/lib.rs`. The F* side does have a real extraction
// (`Alloc.Collections.Binary_heap.fst`).
