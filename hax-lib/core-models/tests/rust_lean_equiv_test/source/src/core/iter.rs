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
