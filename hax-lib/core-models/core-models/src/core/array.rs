use rust_primitives::{sequence::*, slice::*};

/// See [`std::array::TryFromSliceError`]
pub struct TryFromSliceError;

// Dummy type to allow impls
#[hax_lib::exclude]
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
    #[cfg(not(hax_backend_fstar))]
    pub fn map<F: Fn(T) -> U, U>(s: [T; N], f: F) -> [U; N] {
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
    /// See [`std::array::each_ref`]
    pub fn each_ref(s: &[T; N]) -> [&T; N] {
        array_from_fn(|i| array_index(s, i))
    }
}

/// See [`std::array::from_fn`]. The trait bound is `FnMut` (matching std,
/// which is what Aeneas's downstream extraction expects when it reaches
/// into a `Fn` instance via `.FnMutInst`).
#[hax_lib::fstar::replace("let from_fn = Rust_primitives.Slice.array_from_fn")]
pub fn from_fn<T, const N: usize, F: FnMut(usize) -> T>(f: F) -> [T; N] {
    array_from_fn(f)
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

#[cfg(not(hax))]
impl<T: crate::clone::Clone, const N: usize> crate::clone::Clone for [T; N] {
    fn clone(self) -> Self {
        self
    }
}

pub mod equality {
    use rust_primitives::slice::array_index;

    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<T: crate::cmp::PartialEq<U>, U, const N: usize> crate::cmp::PartialEq<[U; N]> for [T; N] {
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

    use proptest::prelude::*;

    proptest! {
        // `map` and `from_fn` cannot be tested with the current solution

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
    }
}
