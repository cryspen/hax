// Dummy type to allow impls
#[hax_lib::exclude]
struct Slice<T>(T);

pub mod iter {
    use crate::option::Option;
    use rust_primitives::{sequence::*, slice::*};

    pub struct Chunks<'a, T> {
        cs: usize,
        elements: &'a [T],
    }
    impl<'a, T> Chunks<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> Chunks<'a, T> {
            Chunks { cs, elements }
        }
    }
    pub struct ChunksExact<'a, T> {
        cs: usize,
        elements: &'a [T],
    }
    impl<'a, T> ChunksExact<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> ChunksExact<'a, T> {
            ChunksExact { cs, elements }
        }
    }
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

    impl<'a, T> crate::iter::traits::iterator::Iterator for Chunks<'a, T> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if slice_length(self.elements) == 0 {
                Option::None
            } else if slice_length(self.elements) < self.cs {
                let res = self.elements;
                self.elements = slice_slice(self.elements, 0, 0);
                Option::Some(res)
            } else {
                let (res, new_elements) = slice_split_at(self.elements, self.cs);
                self.elements = new_elements;
                Option::Some(res)
            }
        }
    }

    impl<'a, T> crate::iter::traits::iterator::Iterator for ChunksExact<'a, T> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if slice_length(self.elements) < self.cs {
                Option::None
            } else {
                let (res, new_elements) = slice_split_at(self.elements, self.cs);
                self.elements = new_elements;
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
    fn chunks<'a>(s: &'a [T], cs: usize) -> iter::Chunks<'a, T> {
        iter::Chunks::new(cs, s)
    }
    fn iter(s: &[T]) -> iter::Iter<T> {
        iter::Iter(rust_primitives::sequence::seq_from_slice(s))
    }
    fn chunks_exact<'a>(s: &'a [T], cs: usize) -> iter::ChunksExact<'a, T> {
        iter::ChunksExact::new(cs, s)
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
    fn split_at_checked(s: &[T], mid: usize) -> Option<(&[T], &[T])> {
        if mid <= s.len() {
            Option::Some(Self::split_at(s, mid))
        } else {
            Option::None
        }
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
    fn get<I: SliceIndex<[T]>>(s: &[T], index: I) -> Option<&<I as SliceIndex<[T]>>::Output> {
        index.get(s)
    }
}

#[hax_lib::attributes]
impl<T> crate::iter::traits::collect::IntoIterator for &[T] {
    type IntoIter = iter::Iter<T>;
    fn into_iter(self) -> Self::IntoIter {
        Slice::iter(self)
    }
}
use crate::option::Option;
use rust_primitives::slice::*;

#[hax_lib::attributes]
pub trait SliceIndex<T: ?Sized> {
    type Output: ?Sized;

    #[hax_lib::requires(true)]
    fn get(self, slice: &T) -> Option<&Self::Output>;
    /* fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
    unsafe fn get_unchecked(self, slice: *const T) -> *const Self::Output;
    unsafe fn get_unchecked_mut(self, slice: *mut T) -> *mut Self::Output;
    fn index(self, slice: &T) -> &Self::Output;
    fn index_mut(self, slice: &mut T) -> &mut Self::Output; */
}

#[hax_lib::attributes]
impl<T> SliceIndex<[T]> for usize {
    type Output = T;
    fn get(self, slice: &[T]) -> Option<&T> {
        if self < slice.len() {
            Option::Some(slice_index(slice, self))
        } else {
            Option::None
        }
    }
}

#[hax_lib::attributes]
impl<T> SliceIndex<[T]> for crate::ops::range::RangeFull {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        Option::Some(slice)
    }
}

#[hax_lib::attributes]
impl<T> SliceIndex<[T]> for crate::ops::range::RangeFrom<usize> {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.start < slice.len() {
            Option::Some(slice_slice(slice, self.start, slice.len()))
        } else {
            Option::None
        }
    }
}
#[hax_lib::attributes]
impl<T> SliceIndex<[T]> for crate::ops::range::RangeTo<usize> {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.end <= slice.len() {
            Option::Some(slice_slice(slice, 0, self.end))
        } else {
            Option::None
        }
    }
}
#[hax_lib::attributes]
impl<T> SliceIndex<[T]> for crate::ops::range::Range<usize> {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.start < self.end && self.end <= slice.len() {
            Option::Some(slice_slice(slice, self.start, self.end))
        } else {
            Option::None
        }
    }
}

use crate::ops::{
    index::Index,
    range::{Range, RangeFrom, RangeFull, RangeTo},
};

#[hax_lib::attributes]
impl<T> Index<Range<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= i.end && i.end <= self.len())]
    fn index(&self, i: Range<usize>) -> &[T] {
        slice_slice(self, i.start, i.end)
    }
}
#[hax_lib::attributes]
impl<T> Index<RangeTo<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.end <= self.len())]
    fn index(&self, i: RangeTo<usize>) -> &[T] {
        slice_slice(self, 0, i.end)
    }
}
#[hax_lib::attributes]
impl<T> Index<RangeFrom<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= self.len())]
    fn index(&self, i: RangeFrom<usize>) -> &[T] {
        slice_slice(self, i.start, slice_length(self))
    }
}
#[hax_lib::attributes]
impl<T> Index<RangeFull> for &[T] {
    type Output = [T];
    fn index(&self, i: RangeFull) -> &[T] {
        slice_slice(self, 0, slice_length(self))
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
