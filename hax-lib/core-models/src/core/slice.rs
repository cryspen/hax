use crate::result::Result;

// Dummy type to allow impls
#[hax_lib::exclude]
struct Slice<T>(T);

pub mod iter {
    use crate::option::Option;
    use rust_primitives::{sequence::*, slice::*};

    /// See [`std::slice::Chunks`]
    pub struct Chunks<'a, T> {
        cs: usize,
        elements: &'a [T],
    }
    impl<'a, T> Chunks<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> Chunks<'a, T> {
            Chunks { cs, elements }
        }
    }
    /// See [`std::slice::ChunksExact`]
    pub struct ChunksExact<'a, T> {
        cs: usize,
        elements: &'a [T],
    }
    impl<'a, T> ChunksExact<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> ChunksExact<'a, T> {
            ChunksExact { cs, elements }
        }
    }
    /// See [`std::slice::Iter`]
    pub struct Iter<'a, T>(pub Seq<&'a T>);

    impl<'a, T> crate::iter::traits::iterator::Iterator for Iter<'a, T> {
        type Item = &'a T;
        fn next(&mut self) -> Option<Self::Item> {
            if seq_len(&self.0) == 0 {
                Option::None
            } else {
                let res = seq_remove(&mut self.0, 0);
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
    /// See [`std::slice::len`]
    fn len(s: &[T]) -> usize {
        rust_primitives::slice::slice_length(s)
    }
    /// See [`std::slice::chunks`]
    fn chunks<'a>(s: &'a [T], cs: usize) -> iter::Chunks<'a, T> {
        iter::Chunks::new(cs, s)
    }
    /// See [`std::slice::iter`]
    fn iter(s: &[T]) -> iter::Iter<'_, T> {
        iter::Iter(rust_primitives::sequence::seq_from_slice(s))
    }
    /// See [`std::slice::chunks_exact`]
    fn chunks_exact<'a>(s: &'a [T], cs: usize) -> iter::ChunksExact<'a, T> {
        iter::ChunksExact::new(cs, s)
    }
    /// See [`std::slice::copy_from_slice`]
    #[hax_lib::requires(Slice::len(s) == Slice::len(src))]
    fn copy_from_slice(s: &mut [T], src: &[T])
    where
        T: Copy,
    {
        slice_clone_from_slice(s, src);
    }
    /// See [`std::slice::clone_from_slice`]
    #[hax_lib::requires(Slice::len(s) == Slice::len(src))]
    fn clone_from_slice(s: &mut [T], src: &[T])
    where
        T: Clone,
    {
        slice_clone_from_slice(s, src);
    }
    /// See [`std::slice::split_at`]
    #[hax_lib::requires(mid <= Slice::len(s))]
    fn split_at(s: &[T], mid: usize) -> (&[T], &[T]) {
        rust_primitives::slice::slice_split_at(s, mid)
    }
    /// See [`std::slice::split_at_checked`]
    fn split_at_checked(s: &[T], mid: usize) -> Option<(&[T], &[T])> {
        if mid <= Slice::len(s) {
            Option::Some(Self::split_at(s, mid))
        } else {
            Option::None
        }
    }
    /// See [`std::slice::is_empty`]
    fn is_empty(s: &[T]) -> bool {
        Self::len(s) == 0
    }
    /// See [`std::slice::contains`]
    #[hax_lib::opaque]
    fn contains(s: &[T], v: &T) -> bool
    where
        T: PartialEq,
    {
        rust_primitives::slice::slice_contains(s, v)
    }
    /// See [`std::slice::copy_within`]
    #[hax_lib::opaque]
    fn copy_within<R>(s: &[T], src: R, dest: usize) -> &[T]
    where
        T: Copy,
    {
        todo!()
    }
    /// See [`std::slice::binary_search`]
    #[hax_lib::opaque]
    fn binary_search(s: &[T], x: &T) -> Result<usize, usize> /* where T: super::ops::Ord */ {
        todo!()
    }
    /// See [`std::slice::get`]
    fn get<I: SliceIndex<[T]>>(s: &[T], index: I) -> Option<&<I as SliceIndex<[T]>>::Output> {
        index.get(s)
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<'a, T> crate::iter::traits::collect::IntoIterator for &'a [T] {
    type IntoIter = iter::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Slice::iter(self)
    }
}
use crate::option::Option;
use rust_primitives::slice::*;

/// See [`std::slice::SliceIndex`]
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
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> SliceIndex<[T]> for crate::ops::range::RangeFull {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        Option::Some(slice)
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> SliceIndex<[T]> for crate::ops::range::RangeFrom<usize> {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.start <= slice.len() {
            Option::Some(slice_slice(slice, self.start, slice.len()))
        } else {
            Option::None
        }
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> SliceIndex<[T]> for crate::ops::range::Range<usize> {
    type Output = [T];
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.start <= self.end && self.end <= slice.len() {
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
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> Index<Range<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= i.end && i.end <= self.len())]
    fn index(&self, i: Range<usize>) -> &[T] {
        slice_slice(self, i.start, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> Index<RangeTo<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.end <= self.len())]
    fn index(&self, i: RangeTo<usize>) -> &[T] {
        slice_slice(self, 0, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> Index<RangeFrom<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= self.len())]
    fn index(&self, i: RangeFrom<usize>) -> &[T] {
        slice_slice(self, i.start, slice_length(self))
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> Index<RangeFull> for &[T] {
    type Output = [T];
    fn index(&self, i: RangeFull) -> &[T] {
        slice_slice(self, 0, slice_length(self))
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T> crate::ops::index::Index<usize> for &[T] {
    type Output = T;
    #[hax_lib::requires(i < self.len())]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::slice_index(self, i)
    }
}

#[cfg(test)]
mod tests {
    use super::Slice;
    use crate::testing::Inject;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_len(slice in prop::collection::vec(any::<u8>(), 0..=20)) {
            prop_assert_eq!(Slice::len(&slice[..]), slice.len());
        }

        #[test]
        fn test_is_empty(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(Slice::is_empty(&slice[..]), slice.is_empty());
        }

        #[test]
        fn test_contains(slice in prop::collection::vec(any::<u8>(), 0..=10), v in any::<u8>()) {
            prop_assert_eq!(Slice::contains(&slice[..], &v), slice.contains(&v));
        }

        #[test]
        fn test_split_at(slice in prop::collection::vec(any::<u8>(), 1..=10)) {
            let mid = slice.len() / 2;
            prop_assert_eq!(Slice::split_at(&slice[..], mid), slice.split_at(mid));
        }

        #[test]
        fn test_split_at_checked(slice in prop::collection::vec(any::<u8>(), 1..=10), mid in 0usize..15) {
            prop_assert_eq!(
                Slice::split_at_checked(&slice[..], mid),
                slice.split_at_checked(mid).inject()
            );
        }

        #[test]
        fn test_copy_from_slice(src in prop::collection::vec(any::<u8>(), 1..=10)) {
            let mut dest = vec![0u8; src.len()];
            Slice::copy_from_slice(&mut dest[..], &src[..]);
            prop_assert_eq!(dest, src);
        }

        #[test]
        fn test_clone_from_slice(src in prop::collection::vec(any::<u8>(), 1..=10)) {
            let mut dest = vec![0u8; src.len()];
            Slice::clone_from_slice(&mut dest[..], &src[..]);
            prop_assert_eq!(dest, src);
        }

        #[test]
        fn test_get_usize(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in any::<usize>()) {
            prop_assert_eq!(
                Slice::get(&slice[..], idx).map(|v: &u8| *v),
                slice.get(idx).copied().inject()
            );
        }

        #[test]
        fn test_get_range(slice in prop::collection::vec(any::<u8>(), 1..=10), start in 0usize..10, end in 0usize..10) {
            prop_assert_eq!(
                Slice::get(&slice[..], crate::ops::range::Range { start, end }),
                slice.get(start..end).inject()
            );
        }

        #[test]
        fn test_get_range_from(slice in prop::collection::vec(any::<u8>(), 1..=10), start in 0usize..15) {
            prop_assert_eq!(
                Slice::get(&slice[..], crate::ops::range::RangeFrom { start }),
                slice.get(start..).inject()
            );
        }

        #[test]
        fn test_get_range_to(slice in prop::collection::vec(any::<u8>(), 1..=10), end in 0usize..15) {
            prop_assert_eq!(
                Slice::get(&slice[..], crate::ops::range::RangeTo { end }),
                slice.get(..end).inject()
            );
        }

        #[test]
        fn test_get_range_full(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(
                Slice::get(&slice[..], crate::ops::range::RangeFull),
                slice.get(..).inject()
            );
        }

        #[test]
        fn test_index_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                crate::ops::index::Index::index(&s, idx),
                &slice[idx]
            );
        }

        #[test]
        fn test_index_range(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..8, len in 0usize..8) {
            let end = (start + len).min(8);
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                crate::ops::index::Index::index(&s, crate::ops::range::Range { start, end }),
                &slice[start..end]
            );
        }

        #[test]
        fn test_index_range_to(slice in prop::collection::vec(any::<u8>(), 8..=8), end in 0usize..=8) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                crate::ops::index::Index::index(&s, crate::ops::range::RangeTo { end }),
                &slice[..end]
            );
        }

        #[test]
        fn test_index_range_from(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..=8) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                crate::ops::index::Index::index(&s, crate::ops::range::RangeFrom { start }),
                &slice[start..]
            );
        }

        #[test]
        fn test_index_range_full(slice in prop::collection::vec(any::<u8>(), 8..=8)) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                crate::ops::index::Index::index(&s, crate::ops::range::RangeFull),
                &slice[..]
            );
        }
    }
}
