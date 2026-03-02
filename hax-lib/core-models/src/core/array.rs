use rust_primitives::{sequence::*, slice::*};

/// See [`std::array::TryFromSliceError`]
pub struct TryFromSliceError;

// Dummy type to allow impls
#[hax_lib::exclude]
struct Dummy<T, const N: usize>([T; N]);

// Dummy impls to get the right disambiguator (https://github.com/cryspen/hax/issues/828)
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}
impl<T> Dummy<T, 0> {}

impl<T, const N: usize> Dummy<T, N> {
    /// See [`std::array::map`]
    pub fn map<F: crate::ops::function::FnOnce<T, Output = U>, U>(
        s: [T; N],
        f: fn(T) -> U, // We cannot use type `F` because it is incompatible with `array_map`
    ) -> [U; N] {
        array_map(s, f)
    }
    /// See [`std::array::as_slice`]
    pub fn as_slice(s: &[T; N]) -> &[T] {
        array_as_slice(s)
    }
}

/// See [`std::array::from_fn`]
pub fn from_fn<T, const N: usize, F: crate::ops::function::FnOnce<usize, Output = T>>(
    f: fn(usize) -> T, // We cannot use type `F` because it is incompatible with `array_from_fn`
) -> [T; N] {
    array_from_fn(f)
}

#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> crate::iter::traits::collect::IntoIterator for [T; N] {
    type IntoIter = iter::IntoIter<T, N>;
    fn into_iter(self) -> iter::IntoIter<T, N> {
        iter::IntoIter(seq_from_array(self))
    }
}

use crate::ops::{
    index::Index,
    range::{Range, RangeFrom, RangeFull, RangeTo},
};

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<usize> for [T; N] {
    type Output = T;
    #[hax_lib::requires(i < self.len())]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::array_index(self, i)
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<Range<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.start <= i.end && i.end <= self.len())]
    fn index(&self, i: Range<usize>) -> &[T] {
        array_slice(self, i.start, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeTo<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.end <= self.len())]
    fn index(&self, i: RangeTo<usize>) -> &[T] {
        array_slice(self, 0, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeFrom<usize>> for [T; N] {
    type Output = [T];
    #[hax_lib::requires(i.start <= self.len())]
    fn index(&self, i: RangeFrom<usize>) -> &[T] {
        array_slice(self, i.start, N)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, const N: usize> Index<RangeFull> for [T; N] {
    type Output = [T];
    fn index(&self, i: RangeFull) -> &[T] {
        array_slice(self, 0, N)
    }
}

mod iter {
    use crate::option::Option;
    use rust_primitives::sequence::*;
    pub struct IntoIter<T, const N: usize>(pub Seq<T>);
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
                super::Dummy::<u8, 4>::as_slice(&model_arr),
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


    }
}
