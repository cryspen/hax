//! Equivalence tests for `core::iter::*`.
//!
//! These mirror the proptest block in `core-models/src/core/iter.rs`.
//! Only `Range::count` is checked against Lean; every other `IteratorMethods`
//! method is Rust-only, for the reason given above the `iterator_methods` module.

use rust_lean_test_macro::rust_lean_test;

// ----- step_by ---------------------------------------------------------------

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

// ----- Rust-only: the lazy adapters ------------------------------------------

// As below, every one of these goes through an `IteratorMethods` call, which the
// Lean side does not have.
#[cfg(test)]
mod adapters {
    #[test]
    fn test_copied_over_slice() {
        let a: [u8; 3] = [1, 2, 3];
        assert_eq!(a.as_slice().iter().copied().count(), 3);
    }

    #[test]
    fn test_cloned_over_slice() {
        let a: [u8; 3] = [1, 2, 3];
        assert_eq!(
            a.as_slice().iter().cloned().collect::<Vec<u8>>(),
            vec![1, 2, 3]
        );
    }

    #[test]
    fn test_filter_map_drops_none() {
        let v: Vec<u32> = (0..6u32)
            .filter_map(|x| if x % 2 == 0 { Some(x) } else { None })
            .collect();
        assert_eq!(v, vec![0, 2, 4]);
    }

    #[test]
    fn test_map_while_stops_at_first_none() {
        let v: Vec<u32> = (0..6u32)
            .map_while(|x| if x < 3 { Some(x) } else { None })
            .collect();
        assert_eq!(v, vec![0, 1, 2]);
    }

    #[test]
    fn test_take_while_and_skip_while_partition() {
        assert_eq!((0..6u32).take_while(|x| *x < 3).count(), 3);
        assert_eq!((0..6u32).skip_while(|x| *x < 3).count(), 3);
    }

    // `skip_while` must not skip again once the predicate has failed.
    #[test]
    fn test_skip_while_only_skips_a_prefix() {
        let v: Vec<u32> = [0u32, 5, 0, 5]
            .into_iter()
            .skip_while(|x| *x == 0)
            .collect();
        assert_eq!(v, vec![5, 0, 5]);
    }

    #[test]
    fn test_scan_threads_state() {
        let v: Vec<u32> = (1..5u32)
            .scan(0u32, |acc, x| {
                *acc += x;
                Some(*acc)
            })
            .collect();
        assert_eq!(v, vec![1, 3, 6, 10]);
    }

    #[test]
    fn test_fuse_stays_exhausted() {
        let mut it = (0..1u32).fuse();
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.next(), None);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_cycle_wraps() {
        assert_eq!((0..3u32).cycle().take(7).count(), 7);
        assert_eq!((0..3u32).cycle().nth(4), Some(1));
    }

    #[test]
    fn test_cycle_of_empty_is_empty() {
        assert_eq!((0..0u32).cycle().next(), None);
    }

    #[test]
    fn test_peek_does_not_consume() {
        let mut it = (0..3u32).peekable();
        assert_eq!(it.peek(), Some(&0));
        assert_eq!(it.peek(), Some(&0));
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.count(), 2);
    }

    #[test]
    fn test_next_if_declines() {
        let mut it = (0..3u32).peekable();
        assert_eq!(it.next_if(|x| *x > 0), None);
        assert_eq!(it.next(), Some(0));
    }

    #[test]
    fn test_next_if_eq() {
        let mut it = (0..3u32).peekable();
        assert_eq!(it.next_if_eq(&0), Some(0));
        assert_eq!(it.next_if_eq(&0), None);
    }

    #[test]
    fn test_inspect_yields_everything() {
        let seen = std::cell::Cell::new(0u32);
        let v: Vec<u32> = (0..4u32).inspect(|_| seen.set(seen.get() + 1)).collect();
        assert_eq!(v, vec![0, 1, 2, 3]);
        assert_eq!(seen.get(), 4);
    }

    #[test]
    fn test_by_ref_leaves_the_rest() {
        let mut it = 0..5u32;
        assert_eq!(it.by_ref().take(2).count(), 2);
        assert_eq!(it.collect::<Vec<u32>>(), vec![2, 3, 4]);
    }
}

// ----- Rust-only: DoubleEndedIterator / ExactSizeIterator --------------------

// Same story as the sources below: reaching `next_back` / `len` needs either an
// `IteratorMethods` call or a hand-written Lean definition, and neither exists
// for these types.
#[cfg(test)]
mod ends {
    #[test]
    fn test_range_next_back() {
        assert_eq!((0..5usize).next_back(), Some(4));
    }

    #[test]
    fn test_empty_range_next_back() {
        assert_eq!((5..5usize).next_back(), None);
    }

    #[test]
    fn test_range_rev_first() {
        assert_eq!((0..5usize).rev().next(), Some(4));
    }

    #[test]
    fn test_range_rev_collect() {
        assert_eq!((0..4u8).rev().collect::<Vec<u8>>(), vec![3, 2, 1, 0]);
    }

    #[test]
    fn test_range_len() {
        assert_eq!((3..10usize).len(), 7);
    }

    #[test]
    fn test_inverted_range_len_is_zero() {
        assert_eq!((10..3usize).len(), 0);
    }

    #[test]
    fn test_signed_range_len_at_edges() {
        assert_eq!((i32::MIN..i32::MAX).len(), u32::MAX as usize);
    }

    #[test]
    fn test_slice_iter_next_back() {
        let a: [u8; 3] = [1, 2, 3];
        assert_eq!(a.as_slice().iter().next_back(), Some(&3));
    }

    #[test]
    fn test_slice_iter_rev_collect() {
        let a: [u8; 3] = [1, 2, 3];
        assert_eq!(
            a.as_slice().iter().rev().copied().collect::<Vec<u8>>(),
            vec![3, 2, 1]
        );
    }

    #[test]
    fn test_nth_back() {
        assert_eq!((0..5usize).nth_back(1), Some(3));
    }

    #[test]
    fn test_nth_back_out_of_range() {
        assert_eq!((0..2usize).nth_back(5), None);
    }

    #[test]
    fn test_rposition_last_match() {
        assert_eq!((0..5usize).rposition(|x| x < 3), Some(2));
    }

    #[test]
    fn test_rposition_no_match() {
        assert_eq!((0..5usize).rposition(|x| x > 10), None);
    }

    #[test]
    fn test_rfold_is_right_to_left() {
        let mut order = Vec::new();
        (0..3usize).rfold((), |(), x| order.push(x));
        assert_eq!(order, vec![2, 1, 0]);
    }
}

// ----- Rust-only: the iterator sources ---------------------------------------

// `core::iter::{empty, once, repeat, …}` build an iterator, but *observing* one
// needs either `Iterator::next` or an `IteratorMethods` method. The Lean side has
// neither for these types: the blanket `impl IteratorMethods for I` is
// `aeneas::exclude`d (see the note further down), and the only hand-written Lean
// iterator definitions in `CoreModels/Core/FunsPrologue.lean` are for
// `ops::range::Range`. So these observations are pinned on the Rust side only.
#[cfg(test)]
mod sources {
    #[test]
    fn test_empty_next() {
        assert_eq!(core::iter::empty::<u8>().next(), None);
    }

    #[test]
    fn test_once_next_then_none() {
        let mut it = core::iter::once(7u8);
        assert_eq!(it.next(), Some(7u8));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_repeat_n_zero_is_empty() {
        assert_eq!(core::iter::repeat_n(7u8, 0).next(), None);
    }

    #[test]
    fn test_repeat_n_count() {
        assert_eq!(core::iter::repeat_n(7u8, 3).count(), 3);
    }

    #[test]
    fn test_repeat_takes_first() {
        assert_eq!(core::iter::repeat(u8::MAX).next(), Some(u8::MAX));
    }

    #[test]
    fn test_successors_none_is_empty() {
        assert_eq!(
            core::iter::successors(None, |x: &u8| Some(*x)).next(),
            crate::helpers::none_u8()
        );
    }

    #[test]
    fn test_successors_doubling() {
        let v: Vec<u8> = core::iter::successors(Some(1u8), |x| x.checked_mul(2)).collect();
        assert_eq!(v, vec![1, 2, 4, 8, 16, 32, 64, 128]);
    }

    #[test]
    fn test_chain_fn_lengths() {
        assert_eq!(core::iter::chain(0..3usize, 0..2usize).count(), 5);
    }

    #[test]
    fn test_zip_fn_stops_at_shorter() {
        assert_eq!(core::iter::zip(0..3usize, 0..5usize).count(), 3);
    }
}

// ----- Rust-only: blocked on the `IteratorMethods` exclusion -----------------

// These come from the blanket `impl IteratorMethods for I`, which is
// `aeneas::exclude`d: each extracts to a missing `Iterator.<method>.default`
// that breaks all of `Funs.lean`, so `skip_lean` cannot apply either.
#[cfg(test)]
mod iterator_methods {
    #[test]
    fn test_fold_sum() {
        assert_eq!((1..5u32).fold(0u32, |acc, x| acc + x), 10);
    }

    #[test]
    fn test_map_sum() {
        assert_eq!((1..4u32).map(|x| x + 1).fold(0u32, |a, b| a + b), 2 + 3 + 4);
    }

    #[test]
    fn test_filter_count() {
        assert_eq!((1..6u32).filter(|x| *x > 2).count(), 3);
    }

    #[test]
    fn test_all_true() {
        assert!((1..4u32).all(|x| x > 0));
    }

    #[test]
    fn test_any_true() {
        assert!((1..4u32).any(|x| x == 2));
    }

    #[test]
    fn test_find_some() {
        assert_eq!((1..4u32).find(|x| *x == 2), Some(2));
    }

    #[test]
    fn test_position_some() {
        assert_eq!((10..40u32).step_by(10).position(|x| x == 20), Some(1));
    }

    #[test]
    fn test_step_by_starts_at_first() {
        let a: [u8; 5] = [10, 11, 12, 13, 14];
        assert_eq!(a.as_slice().iter().step_by(2).next(), Some(&10));
    }

    #[test]
    fn test_take_count() {
        assert_eq!((0..100usize).take(5).count(), 5);
    }

    #[test]
    fn test_skip_count() {
        assert_eq!((0..10usize).skip(3).count(), 7);
    }

    #[test]
    fn test_enumerate_count() {
        assert_eq!((0..4usize).enumerate().count(), 4);
    }

    #[test]
    fn test_zip_count() {
        assert_eq!((0..3usize).zip(0..5usize).count(), 3);
    }

    #[test]
    fn test_chain_count() {
        assert_eq!((0..3usize).chain(0..2usize).count(), 5);
    }

    #[test]
    fn test_min() {
        assert_eq!((1..4u32).min(), Some(1));
    }

    #[test]
    fn test_max() {
        assert_eq!((1..4u32).max(), Some(3));
    }

    #[test]
    fn test_last() {
        assert_eq!((1..4u32).last(), Some(3));
    }

    #[test]
    fn test_nth() {
        assert_eq!((1..4u32).nth(1), Some(2));
    }

    // `slice::iter::Iter` has a higher-ranked lifetime Aeneas cannot translate.
    #[test]
    fn test_fold_sum_over_slice() {
        let v = [1u32, 2, 3, 4];
        assert_eq!(v.iter().fold(0u32, |acc, &x| acc + x), 10);
    }

    #[test]
    fn test_array_iter_count() {
        assert_eq!([1u8, 2, 3].iter().count(), 3);
    }

    // `iter::FromFn` is not in the model.
    #[test]
    fn test_from_fn() {
        let mut n = 0u32;
        let it = core::iter::from_fn(move || {
            n += 1;
            if n <= 3 { Some(n) } else { None }
        });
        assert_eq!(it.fold(0u32, |a, b| a + b), 6);
    }
}
