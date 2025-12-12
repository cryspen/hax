// Dummy type to allow impls
#[hax_lib::exclude]
struct Slice<T>(T);

pub mod iter {
    use crate::option::Option;
    use rust_primitives::sequence::*;

    pub struct Chunks<T>(pub Seq<T>);
    pub struct ChunksExact<T>(pub Seq<T>);
    pub struct Iter<T>(pub Seq<T>);

    impl<T> crate::iter::traits::iterator::Iterator for Iter<T> {
        type Item = T;
        fn next(&mut self) -> Option<Self::Item> {
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

#[hax_lib::attributes]
impl<T> Slice<T> {
    fn len(s: &[T]) -> usize {
        rust_primitives::slice::slice_length(s)
    }
    #[hax_lib::opaque]
    fn chunks(s: &[T], cs: usize) -> iter::Chunks<T> {
        iter::Chunks(rust_primitives::sequence::seq_empty())
    }
    fn iter(s: &[T]) -> iter::Iter<T> {
        iter::Iter(rust_primitives::sequence::seq_from_slice(s))
    }
    #[hax_lib::opaque]
    fn chunks_exact(s: &[T], cs: usize) -> iter::ChunksExact<T> {
        iter::ChunksExact(rust_primitives::sequence::seq_empty())
    }
    #[hax_lib::requires(s.len() == src.len())]
    fn copy_from_slice(s: &mut [T], src: &[T])
    where
        T: crate::marker::Copy,
    {
        rust_primitives::mem::replace(s, src);
    }
    #[hax_lib::requires(s.len() == src.len())]
    fn clone_from_slice(s: &mut [T], src: &[T])
    where
        T: crate::clone::Clone,
    {
        rust_primitives::mem::replace(s, src);
    }
    #[hax_lib::requires(mid <= s.len())]
    fn split_at(s: &[T], mid: usize) -> (&[T], &[T]) {
        rust_primitives::slice::slice_split_at(s, mid)
    }
    fn is_empty(s: &[T]) -> bool {
        s.len() == 0
    }
    #[hax_lib::opaque]
    fn contains(s: &[T], v: T) -> bool {
        rust_primitives::slice::slice_contains(s, v)
    }
    #[hax_lib::opaque]
    fn copy_within<R>(s: &[T], src: R, dest: usize) -> &[T]
    where
        T: Copy,
    {
        todo!()
    }
    #[hax_lib::opaque]
    fn binary_search(s: &[T], x: &T) -> Result<usize, usize> /* where T: super::ops::Ord */ {
        todo!()
    }
    #[hax_lib::opaque]
    fn get<I>(
        s: &[T],
        i: I,
    ) -> crate::option::Option<<Slice<T> as crate::ops::index::Index<I>>::Output>
    where
        Self: crate::ops::index::Index<I>,
    {
        todo!()
    }
}

#[hax_lib::attributes]
impl<T> crate::ops::index::Index<usize> for &[T] {
    type Output = T;
    #[hax_lib::requires(i < self.len())]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::slice_index(self, i)
    }
}
