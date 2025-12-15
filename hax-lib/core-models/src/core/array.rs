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
    pub fn map<U>(s: [T; N], f: fn(T) -> U) -> [U; N] {
        array_map(s, f)
    }
    pub fn as_slice(s: &[T; N]) -> &[T] {
        array_as_slice(s)
    }
}

pub fn from_fn<T, const N: usize>(f: fn(usize) -> T) -> [T; N] {
    array_from_fn(f)
}

impl<T, const N: usize> crate::iter::traits::collect::IntoIterator for [T; N] {
    type IntoIter = iter::IntoIter<T, N>;
    fn into_iter(self) -> iter::IntoIter<T, N> {
        iter::IntoIter(seq_from_array(self))
    }
}

#[hax_lib::attributes]
impl<T, const N: usize> crate::ops::index::Index<usize> for [T; N] {
    type Output = T;
    #[hax_lib::requires(i < self.len())]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::array_index(self, i)
    }
}

mod iter {
    use crate::option::Option;
    use rust_primitives::sequence::*;
    pub struct IntoIter<T, const N: usize>(pub Seq<T>);
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
