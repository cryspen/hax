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
//! Not covered here: `drain` ignores its range argument (only the full range is
//! exercised below), so it is kept opaque for aeneas too — see the Makefile.

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
    fn test_swap_remove(v in prop::collection::vec(any::<u8>(), 1..50), idx in 0usize..50) {
        if idx < v.len() {
            let mut model = v.inject();
            let mut std_v = v.clone();
            prop_assert_eq!(model.swap_remove(idx), std_v.swap_remove(idx));
            prop_assert_eq!(model, std_v.inject());
        }
    }

    #[test]
    fn test_truncate(v in prop::collection::vec(any::<u8>(), 0..50), n in 0usize..60) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.truncate(n);
        std_v.truncate(n);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_clear(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.clear();
        std_v.clear();
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_resize(v in prop::collection::vec(any::<u8>(), 0..50), n in 0usize..60, x in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.resize(n, x);
        std_v.resize(n, x);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_split_off(v in prop::collection::vec(any::<u8>(), 0..50), at in 0usize..50) {
        if at <= v.len() {
            let mut model = v.inject();
            let mut std_v = v.clone();
            let model_tail = model.split_off(at);
            let std_tail = std_v.split_off(at);
            prop_assert_eq!(model, std_v.inject());
            prop_assert_eq!(model_tail, std_tail.inject());
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

// Only the default variant models `Default`: adding the impl to the F* variant
// would shift F*'s positional impl-block numbering and rename every `Vec` method.
#[cfg(not(hax_backend_fstar))]
#[test]
fn test_default() {
    let model: super::Vec<u8> = Default::default();
    let std_v: std::vec::Vec<u8> = Default::default();
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

    // `v[i] = x` goes through the model's `IndexMut`.
    #[test]
    fn test_vec_index_mut(v in prop::collection::vec(any::<u8>(), 1..20), x in any::<u8>()) {
        let i = x as usize % v.len();
        let mut model = v.inject();
        let mut std_v = v.clone();
        model[i] = x;
        std_v[i] = x;
        prop_assert_eq!(model.as_slice(), std_v.as_slice());
    }

    // Small domain and an explicit equal case: `ne` inverts `eq`, so the equal
    // pair is the one worth reaching.
    #[test]
    fn test_vec_ne(
        a in prop::collection::vec(0u8..4, 0..6),
        b in prop::collection::vec(0u8..4, 0..6),
        use_equal in any::<bool>(),
    ) {
        let b = if use_equal { a.clone() } else { b };
        prop_assert_eq!(a.inject() != b.inject(), a != b);
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

// The F* variant models no `IntoIterator` for `Vec`, so its `IntoIter` has to be
// built by hand.
#[cfg(hax_backend_fstar)]
proptest! {
    #[test]
    fn test_into_iter_direct(v in prop::collection::vec(any::<u8>(), 0..30)) {
        let mut it = super::into_iter::IntoIter(
            rust_primitives::sequence::seq_from_boxed_slice(v.clone().into_boxed_slice()),
        );
        let mut collected = std::vec::Vec::new();
        while let Some(x) = it.next() {
            collected.push(x);
        }
        prop_assert_eq!(collected.as_slice(), v.as_slice());
    }
}
// ----- capacity, allocators, conversions, contents ---------------------------
//
// Everything below is modeled by the default `vec` variant only: the F* one
// keeps std's allocator parameter, and several of these methods either return a
// `&mut` (which hax cannot extract) or need a loop that pushes, whose `Seq`
// length side-condition is not provable in F*. See the note on `Default` above.

#[cfg(not(hax_backend_fstar))]
proptest! {
    /// The model's capacity is exact (see the `DEVIATION` note on `capacity`),
    /// so only std's guarantee `len() <= capacity()` can be checked against
    /// real `alloc`.
    #[test]
    fn test_capacity(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let model = v.inject();
        prop_assert_eq!(model.capacity(), v.len());
        prop_assert!(model.capacity() <= v.capacity());
    }

    #[test]
    fn test_reserve(v in prop::collection::vec(any::<u8>(), 0..50), extra in 0usize..50) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.reserve(extra);
        std_v.reserve(extra);
        prop_assert_eq!(model.len(), std_v.len());
        prop_assert!(model.capacity() >= model.len());
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_reserve_exact(v in prop::collection::vec(any::<u8>(), 0..50), extra in 0usize..50) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.reserve_exact(extra);
        std_v.reserve_exact(extra);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_shrink_to_fit(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.shrink_to_fit();
        std_v.shrink_to_fit();
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_shrink_to(v in prop::collection::vec(any::<u8>(), 0..50), min in 0usize..50) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.shrink_to(min);
        std_v.shrink_to(min);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_try_reserve(v in prop::collection::vec(any::<u8>(), 0..50), extra in 0usize..50) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(model.try_reserve(extra).is_ok(), std_v.try_reserve(extra).is_ok());
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_try_reserve_exact(v in prop::collection::vec(any::<u8>(), 0..50), extra in 0usize..50) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(
            model.try_reserve_exact(extra).is_ok(),
            std_v.try_reserve_exact(extra).is_ok()
        );
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_as_mut_slice(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(model.as_mut_slice(), std_v.as_mut_slice());
        // Writes through the returned slice must land in the `Vec`.
        for x in model.as_mut_slice() {
            *x = x.wrapping_add(1);
        }
        for x in std_v.as_mut_slice() {
            *x = x.wrapping_add(1);
        }
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_into_boxed_slice(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let model = v.inject().into_boxed_slice();
        prop_assert_eq!(&*model, &*v.clone().into_boxed_slice());
    }

    #[test]
    fn test_try_remove(v in prop::collection::vec(any::<u8>(), 0..50), idx in 0usize..55) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(model.try_remove(idx), std_v.try_remove(idx));
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_insert_mut(
        v in prop::collection::vec(any::<u8>(), 0..50),
        x in any::<u8>(),
        idx in 0usize..50,
    ) {
        prop_assume!(idx <= v.len());
        let mut model = v.inject();
        let mut std_v = v.clone();
        *model.insert_mut(idx, x) = x.wrapping_add(1);
        *std_v.insert_mut(idx, x) = x.wrapping_add(1);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_push_mut(v in prop::collection::vec(any::<u8>(), 0..50), x in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(*model.push_mut(x), *std_v.push_mut(x));
        *model.push_mut(x) = x.wrapping_add(1);
        *std_v.push_mut(x) = x.wrapping_add(1);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_pop_if(v in prop::collection::vec(any::<u8>(), 0..50), bound in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        prop_assert_eq!(
            model.pop_if(|x| *x > bound),
            std_v.pop_if(|x| *x > bound)
        );
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_resize_with(
        v in prop::collection::vec(any::<u8>(), 0..50),
        new_len in 0usize..60,
        fill in any::<u8>(),
    ) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.resize_with(new_len, || fill);
        std_v.resize_with(new_len, || fill);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_retain(v in prop::collection::vec(any::<u8>(), 0..50), bound in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.retain(|x| *x > bound);
        std_v.retain(|x| *x > bound);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_retain_mut(v in prop::collection::vec(any::<u8>(), 0..50), bound in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.retain_mut(|x| *x > bound);
        std_v.retain_mut(|x| *x > bound);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_extract_if(v in prop::collection::vec(any::<u8>(), 0..50), bound in any::<u8>()) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        let extracted: Vec<u8> = model.extract_if(.., |x| *x > bound).collect();
        let std_extracted: Vec<u8> = std_v.extract_if(.., |x| *x > bound).collect();
        prop_assert_eq!(extracted, std_extracted);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_dedup(v in prop::collection::vec(0u8..4, 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.dedup();
        std_v.dedup();
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_dedup_by(v in prop::collection::vec(0u8..8, 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.dedup_by(|a, b| a / 2 == b / 2);
        std_v.dedup_by(|a, b| *a / 2 == *b / 2);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_dedup_by_key(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.dedup_by_key(|x| x % 3);
        std_v.dedup_by_key(|x| *x % 3);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_extend_from_within(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        model.extend_from_within(..);
        std_v.extend_from_within(..);
        prop_assert_eq!(model, std_v.inject());
    }

    #[test]
    fn test_into_flattened(v in prop::collection::vec(any::<[u8; 3]>(), 0..30)) {
        let model = v.inject().into_flattened();
        let expected = v.clone().into_flattened();
        prop_assert_eq!(model.as_slice(), expected.as_slice());
    }

    #[test]
    fn test_drain_as_slice(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject();
        let mut std_v = v.clone();
        let model_drain = model.drain(..);
        let std_drain = std_v.drain(..);
        prop_assert_eq!(model_drain.as_slice(), std_drain.as_slice());
    }

    #[test]
    fn test_into_iter_as_slice(v in prop::collection::vec(any::<u8>(), 0..50), skip in 0usize..5) {
        let mut model = v.inject().into_iter();
        let mut std_it = v.clone().into_iter();
        for _ in 0..skip {
            prop_assert_eq!(model.next(), std_it.next());
        }
        prop_assert_eq!(model.as_slice(), std_it.as_slice());
    }

    #[test]
    fn test_into_iter_as_mut_slice(v in prop::collection::vec(any::<u8>(), 0..50)) {
        let mut model = v.inject().into_iter();
        let mut std_it = v.clone().into_iter();
        prop_assert_eq!(model.as_mut_slice(), std_it.as_mut_slice());
        for x in model.as_mut_slice() {
            *x = x.wrapping_add(1);
        }
        for x in std_it.as_mut_slice() {
            *x = x.wrapping_add(1);
        }
        prop_assert_eq!(model.as_slice(), std_it.as_slice());
    }
}

/// `Vec::from_fn` postdates the toolchain this crate is built with, so the
/// expected behaviour is pinned directly rather than compared against std.
#[cfg(not(hax_backend_fstar))]
proptest! {
    #[test]
    fn test_from_fn(n in 0usize..50) {
        let model = super::Vec::from_fn(n, |i| (i % 7) as u8);
        let expected: Vec<u8> = (0..n).map(|i| (i % 7) as u8).collect();
        prop_assert_eq!(model.as_slice(), expected.as_slice());
    }
}

#[cfg(not(hax_backend_fstar))]
#[test]
fn test_try_with_capacity() {
    let model: super::Vec<u8> = super::Vec::try_with_capacity(10).unwrap();
    let std_v: Vec<u8> = Vec::try_with_capacity(10).unwrap();
    assert_eq!(model, std_v.inject());
}

// The model's `Vec` drops the allocator argument (see the `DEVIATION` note on
// `new_in`), so only the resulting contents can be compared.
#[cfg(not(hax_backend_fstar))]
#[test]
fn test_allocator_constructors() {
    let std_v: Vec<u8> = Vec::new_in(std::alloc::Global);
    assert_eq!(
        super::Vec::<u8>::new_in(crate::alloc::Global),
        std_v.inject()
    );
    let std_v: Vec<u8> = Vec::with_capacity_in(7, std::alloc::Global);
    assert_eq!(
        super::Vec::<u8>::with_capacity_in(7, crate::alloc::Global),
        std_v.inject()
    );
    let std_v: Vec<u8> = Vec::try_with_capacity_in(7, std::alloc::Global).unwrap();
    assert_eq!(
        super::Vec::<u8>::try_with_capacity_in(7, crate::alloc::Global).unwrap(),
        std_v.inject()
    );
}

/// `Vec`, `Drain`, `IntoIter` and `ExtractIf` all report the global allocator:
/// the model has no other one.
#[cfg(not(hax_backend_fstar))]
#[test]
fn test_allocator() {
    let mut model: super::Vec<u8> = vec![1u8, 2, 3].inject();
    assert_eq!(model.allocator(), crate::alloc::Global);
    assert_eq!(
        model.extract_if(.., |x| *x == 1).allocator(),
        crate::alloc::Global
    );
    assert_eq!(model.drain(..).allocator(), crate::alloc::Global);
    assert_eq!(model.into_iter().allocator(), crate::alloc::Global);
}

// ----- panics ----------------------------------------------------------------

fn vec_of(n: usize) -> (super::Vec<u8>, Vec<u8>) {
    let real: Vec<u8> = (0..n as u8).collect();
    (real.inject(), real)
}

#[test]
fn test_insert_past_end_panics() {
    let (mut model, mut real) = vec_of(3);
    let i = std::hint::black_box(4usize);
    crate::testing::panics_like_core(|| model.insert(i, 9), || real.insert(i, 9));
}

#[test]
fn test_split_off_past_end_panics() {
    let (mut model, mut real) = vec_of(3);
    let at = std::hint::black_box(4usize);
    crate::testing::panics_like_core(|| model.split_off(at), || real.split_off(at));
}

#[test]
fn test_index_out_of_bounds_panics() {
    let (model, real) = vec_of(3);
    let i = std::hint::black_box(3usize);
    crate::testing::panics_like_core(|| model[i], || real[i]);
}

#[test]
fn test_remove_past_end_panics() {
    let (mut model, mut real) = vec_of(3);
    let i = std::hint::black_box(3usize);
    crate::testing::panics_like_core(|| model.remove(i), || real.remove(i));
}
