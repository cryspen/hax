use rust_primitives::{sequence::*, slice::*};

/// See [`std::array::TryFromSliceError`]
pub struct TryFromSliceError;

// Dummy type to allow impls
// F*-only: `charon::exclude` would drop this dummy type while its `impl`
// blocks still reference it (see f32.rs).
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
// Dummy type to allow impls. The name has to be `Array`, not `array`: aeneas
// translates real core's `[T; N]` inherent impls to `core.array.Array.*`, and
// that name is what makes those calls land on the definitions below. (So the
// coverage tool, which keys these methods `array::*` after the primitive, needs
// an alias rather than a rename here.)
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct Array<T, const N: usize>([T; N]);

// Array impls to get the right disambiguator (https://github.com/cryspen/hax/issues/828)
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}

impl<T, const N: usize> Array<T, N> {
    /// See [`std::array::map`]
    // `FnMut`, like std: a `Fn` bound rejects inferred closures.
    #[cfg(not(hax_backend_fstar))]
    pub fn map<F: FnMut(T) -> U, U>(s: [T; N], f: F) -> [U; N] {
        array_map(s, f)
    }
    #[cfg(hax_backend_fstar)]
    pub fn map<F: crate::ops::function::FnOnce<T, Output = U>, U>(
        s: [T; N],
        f: fn(T) -> U,
    ) -> [U; N] {
        array_map(s, f)
    }
    /// See [`std::array::as_slice`]
    pub fn as_slice(s: &[T; N]) -> &[T] {
        array_as_slice(s)
    }
    /// See [`std::array::as_mut_slice`]
    // `&mut` returns are unsupported in the F* backend.
    #[cfg(not(hax_backend_fstar))]
    pub fn as_mut_slice(s: &mut [T; N]) -> &mut [T] {
        array_as_slice_mut(s)
    }
    /// See [`std::array::each_ref`]
    pub fn each_ref(s: &[T; N]) -> [&T; N] {
        array_from_fn(|i| array_index(s, i))
    }
}

#[hax_lib::fstar::replace("let from_fn = Rust_primitives.Slice.array_from_fn")]
pub fn from_fn<T, const N: usize, F: FnMut(usize) -> T>(f: F) -> [T; N] {
    array_from_fn(f)
}

/// See [`std::array::from_ref`]
pub fn from_ref<T>(s: &T) -> &[T; 1] {
    array_from_ref(s)
}

/// See [`std::array::from_mut`]
// `&mut` returns are unsupported in the F* backend.
#[cfg(not(hax_backend_fstar))]
pub fn from_mut<T>(s: &mut T) -> &mut [T; 1] {
    array_from_mut(s)
}

/// See [`std::array::repeat`]
// The bound is Rust's `Clone`, not the model's: the model's `clone` consumes its
// receiver, so `N` copies cannot be made from one owned value through it.
pub fn repeat<T: Clone, const N: usize>(val: T) -> [T; N] {
    array_repeat(val)
}

#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, const N: usize> crate::iter::traits::collect::IntoIterator for [T; N] {
    type Item = T;
    type IntoIter = iter::IntoIter<T, N>;
    fn into_iter(self) -> iter::IntoIter<T, N> {
        iter::IntoIter(seq_from_array(self))
    }
}

use crate::ops::{
    index::Index,
    range::{Range, RangeFrom, RangeFull, RangeTo},
};

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, I, const N: usize> crate::ops::index::Index<I> for [T; N]
where
    [T]: Index<I>,
{
    type Output = <[T] as Index<I>>::Output;
    fn index(&self, i: I) -> &Self::Output {
        self.as_slice().index(i)
    }
}

#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
impl<T, const N: usize> Index<usize> for [T; N] {
    type Output = T;
    #[hax_lib::requires(i < N)]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::array_index(self, i)
    }
}

#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<Range<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.start <= i.end && i.end <= N)]
    fn index(&self, i: Range<usize>) -> &[T] {
        array_slice(self, i.start, i.end)
    }
}
#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeTo<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.end <= N)]
    fn index(&self, i: RangeTo<usize>) -> &[T] {
        array_slice(self, 0, i.end)
    }
}
#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeFrom<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.start <= N)]
    fn index(&self, i: RangeFrom<usize>) -> &[T] {
        array_slice(self, i.start, N)
    }
}
#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeFull> for [T; N] {
    type Output = [T];
    fn index(&self, i: RangeFull) -> &[T] {
        array_slice(self, 0, N)
    }
}

// Not for `hax_backend_fstar`: that model's blanket `impl<T> Clone for T`
// already covers arrays, and both in scope fails coherence.
#[cfg(not(hax_backend_fstar))]
impl<T: crate::clone::Clone, const N: usize> crate::clone::Clone for [T; N] {
    fn clone(self) -> Self {
        self
    }
}

pub mod equality {
    use rust_primitives::slice::array_index;

    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<T: crate::cmp::PartialEq<U>, U, const N: usize> crate::cmp::PartialEq<[U; N]> for [T; N] {
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &[U; N]) -> bool {
            self.eq(other) == false
        }
        fn eq(&self, other: &[U; N]) -> bool {
            let mut i = 0;
            while i < N {
                if !array_index(self, i).eq(array_index(other, i)) {
                    return false;
                }
                i += 1;
            }
            true
        }
    }
}

mod iter {
    use crate::option::Option;
    use rust_primitives::sequence::*;
    /// The elements not yet yielded, in order.
    pub struct IntoIter<T, const N: usize>(pub Seq<T>);
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T, const N: usize> crate::iter::traits::iterator::Iterator for IntoIter<T, N> {
        type Item = T;
        fn next(&mut self) -> Option<T> {
            if seq_len(&self.0) == 0 {
                Option::None
            } else {
                let res = seq_remove(&mut self.0, 0);
                Option::Some(res)
            }
        }
    }

    // Kept after the `Iterator` impl: the F* backend names inherent methods by
    // impl-block order, so a block inserted before it would renumber `impl`.
    impl<T, const N: usize> IntoIter<T, N> {
        /// See [`std::array::IntoIter::new`]
        pub fn new(arr: [T; N]) -> IntoIter<T, N> {
            IntoIter(seq_from_array(arr))
        }
        /// See [`std::array::IntoIter::empty`]
        pub fn empty() -> IntoIter<T, N> {
            IntoIter(seq_empty())
        }
        /// See [`std::array::IntoIter::as_slice`]
        pub fn as_slice(&self) -> &[T] {
            seq_to_slice(&self.0)
        }
        /// See [`std::array::IntoIter::as_mut_slice`]
        // `&mut` returns are unsupported in the F* backend.
        #[cfg(not(hax_backend_fstar))]
        pub fn as_mut_slice(&mut self) -> &mut [T] {
            seq_to_slice_mut(&mut self.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;

    impl<T: Inject, const N: usize> Inject for [T; N] {
        type Model = [T::Model; N];
        fn inject(&self) -> Self::Model {
            std::array::from_fn(|i| self[i].inject())
        }
    }

    use crate::iter::traits::iterator::Iterator as ModelIterator;
    use crate::option::Option as ModelOption;
    use proptest::prelude::*;

    // Equal arrays are the case `ne` inverts, so reach that case explicitly.
    #[cfg(not(hax_backend_fstar))]
    proptest! {
        #[test]
        fn test_array_ne(a in any::<[u8; 3]>(), b in any::<[u8; 3]>(), use_equal in any::<bool>()) {
            let b = if use_equal { a } else { b };
            prop_assert_eq!(
                <[u8; 3] as crate::cmp::PartialEq<[u8; 3]>>::ne(&a, &b),
                a != b
            );
        }
    }

    // Under the F* cfg `map` takes a `fn` pointer plus a phantom `F: FnOnce<..>`
    // parameter (the backend types the function through it). Nothing in the model
    // implements that trait, so the test supplies a witness.
    #[cfg(hax_backend_fstar)]
    mod fstar_map {
        use crate::testing::Inject;
        use proptest::prelude::*;

        fn triple(x: u8) -> u8 {
            x.wrapping_mul(3)
        }

        struct Triple;

        impl crate::ops::function::FnOnce<u8> for Triple {
            type Output = u8;
            fn call_once(&self, args: u8) -> u8 {
                triple(args)
            }
        }

        proptest! {

            #[test]
            fn test_map(arr in any::<[u8; 4]>()) {
                prop_assert_eq!(
                    super::super::Array::<u8, 4>::map::<Triple, u8>(arr.inject(), triple),
                    arr.map(triple)
                );
            }

            #[test]
            fn test_witness_call_once(x in any::<u8>()) {
                prop_assert_eq!(
                    crate::ops::function::FnOnce::call_once(&Triple, x),
                    triple(x)
                );
            }
        }
    }

    /// `IntoIter` is lazy; draining it is what observes it.
    fn drain<I: ModelIterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let ModelOption::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

    /// `u8`'s `Clone` is the identity, which cannot tell "`N` clones" from
    /// "`N - 1` clones plus the original value" — `repeat`'s actual contract.
    #[derive(Debug, PartialEq)]
    struct Bump(u8);

    impl Clone for Bump {
        fn clone(&self) -> Bump {
            Bump(self.0 + 1)
        }
    }

    proptest! {
        // Under the F* cfg `map` takes a `fn`, which this closure can't coerce to.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_map(arr in any::<[u8; 4]>(), table in any::<[u8; 256]>()) {
            let f = |x: u8| table[x as usize];
            prop_assert_eq!(super::Array::<u8, 4>::map(arr.inject(), f), arr.map(f));
        }

        #[test]
        fn test_from_fn(table in any::<[u8; 256]>()) {
            let f = |i: usize| table[i];
            let model: [u8; 4] = super::from_fn(f);
            prop_assert_eq!(model, std::array::from_fn::<u8, 4, _>(f));
        }

        #[test]
        fn test_clone(arr in any::<[u8; 4]>()) {
            prop_assert_eq!(
                crate::clone::Clone::clone(arr.inject()),
                arr.clone().inject()
            );
        }

        #[test]
        fn test_as_slice(arr in any::<[u8; 4]>()) {
            let model_arr = arr.inject();
            prop_assert_eq!(
                super::Array::<u8, 4>::as_slice(&model_arr),
                arr.as_slice()
            );
        }

        #[test]
        fn test_index_usize(arr in any::<[u8; 4]>(), idx in 0usize..4) {
            let model_arr = arr.inject();
            prop_assert_eq!(model_arr[idx], arr[idx]);
        }

        #[test]
        fn test_index_range(arr in any::<[u8; 8]>(), start in 0usize..8, len in 0usize..8) {
            let end = (start + len).min(8);
            let model_arr = arr.inject();
            prop_assert_eq!(&model_arr[start..end], &arr[start..end]);
        }

        #[test]
        fn test_index_range_to(arr in any::<[u8; 8]>(), end in 0usize..=8) {
            let model_arr = arr.inject();
            prop_assert_eq!(&model_arr[..end], &arr[..end]);
        }

        #[test]
        fn test_index_range_from(arr in any::<[u8; 8]>(), start in 0usize..=8) {
            let model_arr = arr.inject();
            prop_assert_eq!(&model_arr[start..], &arr[start..]);
        }

        #[test]
        fn test_index_range_full(arr in any::<[u8; 8]>()) {
            let model_arr = arr.inject();
            prop_assert_eq!(&model_arr[..], &arr[..]);
        }

        #[test]
        fn test_each_ref(arr in any::<[u8; 4]>()) {
            let model_arr = arr.inject();
            let model_refs = super::Array::<u8, 4>::each_ref(&model_arr);
            let std_refs = arr.each_ref();
            for i in 0..4 {
                prop_assert_eq!(*model_refs[i], *std_refs[i]);
            }
        }

        #[test]
        fn test_eq(a in any::<[u8; 4]>(), b in any::<[u8; 4]>()) {
            let ma = a.inject();
            let mb = b.inject();
            prop_assert_eq!(crate::cmp::PartialEq::eq(&ma, &mb), a == b);
        }

        // Two independent arrays are essentially never equal, so the `true` exit
        // of the comparison loop needs a reflexive case.
        #[test]
        fn test_eq_reflexive(a in any::<[u8; 4]>()) {
            let ma = a.inject();
            prop_assert_eq!(crate::cmp::PartialEq::eq(&ma, &ma), a == a);
        }

        #[test]
        fn test_into_iter(arr in any::<[u8; 4]>()) {
            let mut it = crate::iter::traits::collect::IntoIterator::into_iter(arr.inject());
            let mut collected = std::vec::Vec::new();
            while let crate::option::Option::Some(x) =
                crate::iter::traits::iterator::Iterator::next(&mut it)
            {
                collected.push(x);
            }
            prop_assert_eq!(collected, arr.into_iter().collect::<std::vec::Vec<u8>>());
        }

        // `arr[idx]` above resolves to std's indexing; these spell out the
        // model's `Index` impls for `[T; N]`.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_model_index_usize(arr in any::<[u8; 4]>(), idx in 0usize..4) {
            let m = arr.inject();
            prop_assert_eq!(
                <[u8; 4] as crate::ops::index::Index<usize>>::index(&m, idx),
                &arr[idx]
            );
        }

        // `as_mut_slice` / `from_mut` have no F* model (`&mut` returns).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_as_mut_slice(arr in any::<[u8; 4]>(), v in any::<u8>()) {
            let mut model_arr = arr.inject();
            let mut std_arr = arr;
            super::Array::<u8, 4>::as_mut_slice(&mut model_arr).fill(v);
            std_arr.as_mut_slice().fill(v);
            prop_assert_eq!(model_arr, std_arr);
        }

        #[test]
        fn test_from_ref(x in any::<u8>()) {
            let model_x = x.inject();
            prop_assert_eq!(super::from_ref(&model_x), std::array::from_ref(&x));
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_from_mut(x in any::<u8>(), v in any::<u8>()) {
            let mut model_x = x.inject();
            let mut std_x = x;
            super::from_mut(&mut model_x)[0] = v;
            std::array::from_mut(&mut std_x)[0] = v;
            prop_assert_eq!(model_x, std_x);
        }

        #[test]
        fn test_repeat(x in any::<u8>()) {
            prop_assert_eq!(super::repeat::<u8, 5>(x.inject()), std::array::repeat::<u8, 5>(x));
        }

        // Pins `repeat`'s clone discipline: `N - 1` clones and then `val`.
        #[test]
        fn test_repeat_clones(x in 0u8..200) {
            prop_assert_eq!(
                super::repeat::<Bump, 3>(Bump(x)),
                std::array::repeat::<Bump, 3>(Bump(x))
            );
        }

        #[test]
        fn test_repeat_zero(x in any::<u8>()) {
            prop_assert_eq!(super::repeat::<u8, 0>(x.inject()), std::array::repeat::<u8, 0>(x));
        }

        // ----- IntoIter ------------------------------------------------------

        // `IntoIter::new` is deprecated in std but still part of its API.
        #[allow(deprecated)]
        #[test]
        fn test_into_iter_new(arr in any::<[u8; 4]>()) {
            prop_assert_eq!(
                drain(super::iter::IntoIter::new(arr.inject())),
                std::array::IntoIter::new(arr).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_into_iter_as_slice(arr in any::<[u8; 4]>(), taken in 0usize..=4) {
            let mut model = super::iter::IntoIter::new(arr.inject());
            let mut std_it = arr.into_iter();
            for _ in 0..taken {
                model.next();
                std_it.next();
            }
            prop_assert_eq!(model.as_slice(), std_it.as_slice());
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_model_index_range(arr in any::<[u8; 8]>(), start in 0usize..8, len in 0usize..8) {
            let end = (start + len).min(8);
            let m = arr.inject();
            prop_assert_eq!(
                <[u8; 8] as crate::ops::index::Index<crate::ops::range::Range<usize>>>::index(
                    &m,
                    crate::ops::range::Range { start, end }
                ),
                &arr[start..end]
            );
        }

        // The F* variant has one `Index` impl per range kind, all going through
        // `rust_primitives::slice::array_slice`.
        #[cfg(hax_backend_fstar)]
        #[test]
        fn test_model_index_range(arr in any::<[u8; 8]>(), start in 0usize..8, len in 0usize..8) {
            let end = (start + len).min(8);
            let m = arr.inject();
            prop_assert_eq!(
                crate::ops::index::Index::index(&m, crate::ops::range::Range { start, end }),
                &arr[start..end]
            );
            prop_assert_eq!(
                crate::ops::index::Index::index(&m, crate::ops::range::RangeTo { end }),
                &arr[..end]
            );
            prop_assert_eq!(
                crate::ops::index::Index::index(&m, crate::ops::range::RangeFrom { start }),
                &arr[start..]
            );
            prop_assert_eq!(
                crate::ops::index::Index::index(&m, crate::ops::range::RangeFull),
                &arr[..]
            );
        }

        #[cfg(hax_backend_fstar)]
        #[test]
        fn test_model_index_usize(arr in any::<[u8; 4]>(), idx in 0usize..4) {
            let m = arr.inject();
            prop_assert_eq!(crate::ops::index::Index::index(&m, idx), &arr[idx]);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_into_iter_as_mut_slice(arr in any::<[u8; 4]>(), taken in 0usize..=4, v in any::<u8>()) {
            let mut model = super::iter::IntoIter::new(arr.inject());
            let mut std_it = arr.into_iter();
            for _ in 0..taken {
                model.next();
                std_it.next();
            }
            model.as_mut_slice().fill(v);
            std_it.as_mut_slice().fill(v);
            prop_assert_eq!(drain(model), std_it.collect::<Vec<_>>());
        }
    }

    #[test]
    fn test_into_iter_empty() {
        assert_eq!(
            drain(super::iter::IntoIter::<u8, 4>::empty()),
            std::array::IntoIter::<u8, 4>::empty().collect::<Vec<_>>()
        );
    }
}
