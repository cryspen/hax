//! Test suite shared by the two `vec` models.
//!
//! `vec` exists in two cfg-exclusive variants: the default one, whose `Vec`
//! has a single type parameter, and the `hax_backend_fstar` one, which keeps
//! std's explicit allocator parameter (`Vec<T, A = Global>`). Both are
//! declared as `mod tests;` from inside `mod vec`, resolving to `src/vec/tests.rs`, so exactly one is
//! compiled per cfg and these tests run against whichever is selected.
//!
//! The tests only ever spell the type as `super::Vec<T>`, which resolves to
//! `Vec<T>` in the default variant and to `Vec<T, Global>` in the F\* one —
//! identical surface, so nothing here needs to know which is in play.
//!
//! Not covered here: `truncate`, `clear`, `resize` and `swap_remove` are
//! `#[hax_lib::opaque]` stubs whose Rust bodies deliberately do not implement
//! std's behaviour, and `drain` ignores its range argument (only the full
//! range is exercised below). Comparing those against std would fail by
//! construction.

use crate::testing::Inject;
use proptest::prelude::*;

impl<T: Clone> Inject for Vec<T> {
    type Model = super::Vec<T>;
    fn inject(&self) -> super::Vec<T> {
        super::Vec::<T>(
            rust_primitives::sequence::seq_from_boxed_slice(self.clone().into_boxed_slice()),
            #[cfg(hax_backend_fstar)]
            std::marker::PhantomData,
        )
    }
}

proptest! {
    #[test]
    fn test_len(v in prop::collection::vec(any::<u8>(), 0..100)) {
        prop_assert_eq!(v.inject().len(), v.len());
    }

    #[test]
    fn test_is_empty(v in prop::collection::vec(any::<u8>(), 0..100)) {
        prop_assert_eq!(v.inject().is_empty(), v.is_empty());
    }

    #[test]
    fn test_as_slice(v in prop::collection::vec(any::<u8>(), 0..100)) {
        let model = v.inject();
        prop_assert_eq!(model.as_slice(), v.as_slice());
    }

    #[test]
    fn test_push(v in prop::collection::vec(any::<u8>(), 0..50), x in any::<u8>()) {
        let mut model = v.inject();
        model.push(x);
        let mut std_v = v.clone();
        std_v.push(x);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_pop(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(model.pop(), std_v.pop());
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_index(v in prop::collection::vec(any::<u8>(), 1..50)) {
        let model = v.inject();
        for i in 0..v.len() {
            prop_assert_eq!(model[i], v[i]);
        }
    }

    #[test]
    fn test_index_range(v in prop::collection::vec(any::<u8>(), 0..50), start in 0usize..50, len in 0usize..50) {
        let start = start.min(v.len());
        let end = (start + len).min(v.len());
        let model = v.inject();
        prop_assert_eq!(&model[start..end], &v[start..end]);
    }

    #[test]
    fn test_insert(v in prop::collection::vec(any::<u8>(), 0..50), x in any::<u8>(), idx in 0usize..50) {
        if idx <= v.len() {
            let mut model = v.inject();
            model.insert(idx, x);
            let mut std_v = v.clone();
            std_v.insert(idx, x);
            prop_assert_eq!(model, std_v.inject());
        }
    }

    #[test]
    fn test_remove(v in prop::collection::vec(any::<u8>(), 1..50), idx in 0usize..50) {
        if idx < v.len() {
            let mut model = v.inject();
            let mut std_v = v.clone();
            prop_assert_eq!(model.remove(idx), std_v.remove(idx));
            prop_assert_eq!(model, std_v.inject());
        }
    }

    #[test]
    fn test_append(v1 in prop::collection::vec(any::<u8>(), 0..50), v2 in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model1 = v1.inject();
        model1.append(&mut v2.inject());
        let mut std_v = v1.clone();
        std_v.append(&mut v2.clone());
        prop_assert_eq!(model1, std_v.inject());
    }

    #[test]
    fn test_extend_from_slice(v in prop::collection::vec(any::<u8>(), 0..50), ext in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        model.extend_from_slice(&ext);
        let mut std_v = v.clone();
        std_v.extend_from_slice(&ext);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_from_elem(x in any::<u8>(), len in 0usize..100) {
        let model = super::from_elem(x, len);
        prop_assert_eq!(model, vec![x; len].inject());
    }

    #[test]
    fn test_from_iter(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let model: super::Vec<u8> = v.iter().copied().collect();
        prop_assert_eq!(model, v.inject());
    }

    /// `drain` ignores its range argument, so only the full range agrees
    /// with std. The drained elements and the emptied `Vec` are both checked.
    #[test]
    fn test_drain_full(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let drained: std::vec::Vec<u8> = model.drain(..).collect();
        prop_assert_eq!(drained.as_slice(), v.as_slice());
        prop_assert_eq!(model, std::vec::Vec::new().inject());
    }
}

#[test]
fn test_new() {
    let model: super::Vec<u8> = super::Vec::new();
    let std_v: std::vec::Vec<u8> = std::vec::Vec::new();
    assert_eq!(model, std_v.inject());
}

#[test]
fn test_with_capacity() {
    let model: super::Vec<u8> = super::Vec::with_capacity(10);
    let std_v: std::vec::Vec<u8> = std::vec::Vec::with_capacity(10);
    assert_eq!(model, std_v.inject());
}

// ----- Clone / PartialEq / IntoIterator -------
//
// The F* variant of `vec` models none of these three, so the tests below are
// specific to the default variant. (Its `PartialEq` is what `prop_assert_eq!`
// uses above; under `hax_backend_fstar` that comes from a `cfg(test)` derive.)

#[cfg(not(hax_backend_fstar))]
proptest! {
    #[test]
    fn test_vec_clone(v in prop::collection::vec(any::<u8>(), 0..30)) {
        // Compare the clone's contents to std directly (independent of
        // the model's own `PartialEq`, which is tested separately).
        let cloned = v.inject().clone();
        prop_assert_eq!(cloned.as_slice(), v.as_slice());
    }

    #[test]
    fn test_vec_eq(
        a in prop::collection::vec(any::<u8>(), 0..15),
        b in prop::collection::vec(any::<u8>(), 0..15),
    ) {
        prop_assert_eq!(a.inject() == b.inject(), a == b);
    }

    #[test]
    fn test_vec_into_iter(v in prop::collection::vec(any::<u8>(), 0..30)) {
        let mut it = v.inject().into_iter();
        let mut collected: std::vec::Vec<u8> = std::vec::Vec::new();
        while let Some(x) = it.next() {
            collected.push(x);
        }
        prop_assert_eq!(collected.as_slice(), v.as_slice());
    }
}
