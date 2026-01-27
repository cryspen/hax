use rust_primitives::{sequence::*, slice::*};

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
    pub fn map<F: crate::ops::function::FnOnce<T, Output = U>, U>(
        s: [T; N],
        f: fn(T) -> U, // We cannot use type `F` because it is incompatible with `array_map`
    ) -> [U; N] {
        array_map(s, f)
    }
    pub fn as_slice(s: &[T; N]) -> &[T] {
        array_as_slice(s)
    }
}

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
                let res = seq_first(&self.0);
                self.0 = seq_slice(&self.0, 1, seq_len(&self.0));
                Option::Some(res)
            }
        }
    }
}
