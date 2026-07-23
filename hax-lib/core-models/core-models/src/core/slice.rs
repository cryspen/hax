use crate::result::Result;

// Dummy type to allow impls
#[hax_lib::exclude]
struct Slice<T>([T]);

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

    /// See [`std::slice::Windows`]
    pub struct Windows<'a, T> {
        size: usize,
        elements: &'a [T],
    }
    impl<'a, T> Windows<'a, T> {
        pub fn new(size: usize, elements: &'a [T]) -> Windows<'a, T> {
            Windows { size, elements }
        }
    }
    // opaque: F* cannot prove slice bounds (1 <= length) in the else branch
    // This needs the invariant that size > 0
    #[hax_lib::opaque]
    impl<'a, T> crate::iter::traits::iterator::Iterator for Windows<'a, T> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if slice_length(self.elements) < self.size {
                Option::None
            } else {
                let res = slice_slice(self.elements, 0, self.size);
                self.elements = slice_slice(self.elements, 1, slice_length(self.elements));
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
    /// See [`std::slice::get_unchecked`]
    // opaque for F*: the generic precondition isn't provable here (the concrete
    // `SliceIndex` impls verify).
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(index.get(s).is_some())]
    fn get_unchecked<I: SliceIndex<[T]>>(s: &[T], index: I) -> &<I as SliceIndex<[T]>>::Output {
        index.get_unchecked(s)
    }
    // `&mut` returns are unsupported in the F* backend.
    /// See [`std::slice::get_mut`]
    #[cfg(not(hax_backend_fstar))]
    fn get_mut<I: SliceIndex<[T]>>(
        s: &mut [T],
        index: I,
    ) -> Option<&mut <I as SliceIndex<[T]>>::Output> {
        index.get_mut(s)
    }
    /// See [`std::slice::get_unchecked_mut`]
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(index.get(s).is_some())]
    fn get_unchecked_mut<I: SliceIndex<[T]>>(
        s: &mut [T],
        index: I,
    ) -> &mut <I as SliceIndex<[T]>>::Output {
        index.get_unchecked_mut(s)
    }
    /// See [`std::slice::first`]
    fn first(s: &[T]) -> Option<&T> {
        if Self::is_empty(s) {
            Option::None
        } else {
            Option::Some(slice_index(s, 0))
        }
    }
    /// See [`std::slice::last`]
    fn last(s: &[T]) -> Option<&T> {
        if Self::is_empty(s) {
            Option::None
        } else {
            Option::Some(slice_index(s, Self::len(s) - 1))
        }
    }
    /// See [`std::slice::swap`]
    // opaque for F*: `&mut` mutation is unsupported there.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(a < Slice::len(s) && b < Slice::len(s))]
    fn swap(s: &mut [T], a: usize, b: usize) {
        rust_primitives::slice::slice_swap(s, a, b);
    }
    /// See [`std::slice::reverse`]
    // opaque for F*: see `swap`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn reverse(s: &mut [T]) {
        rust_primitives::slice::slice_reverse(s);
    }
    /// See [`std::slice::windows`]
    #[hax_lib::requires(size > 0)]
    fn windows<'a>(s: &'a [T], size: usize) -> iter::Windows<'a, T> {
        if size == 0 {
            crate::panicking::internal::panic()
        }
        iter::Windows::new(size, s)
    }
    /// See [`std::slice::fill`]
    // opaque: for-loop + indexed mutation causes F* dependency cycle through Rust_primitives.Hax
    #[hax_lib::opaque]
    fn fill(s: &mut [T], value: T)
    where
        T: Clone,
    {
        for i in 0..s.len() {
            s[i] = value.clone();
        }
    }

    // F* names inherent methods by impl-block order, so `starts_with`/`ends_with`
    // live in this first block (as opaque vals) for F* to keep their `impl__`
    // name. The aeneas/lean copies are in the `cfg(not(hax_backend_fstar))` block
    // after the `PartialEq for [T]` impl, where source order avoids a forward
    // reference to `eq`.
    /// See [`std::slice::starts_with`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::opaque]
    fn starts_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        Self::len(s) >= n && slice_slice(s, 0, n) == needle
    }
    /// See [`std::slice::ends_with`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::opaque]
    fn ends_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        let l = Self::len(s);
        l >= n && slice_slice(s, l - n, l) == needle
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<U, T: crate::cmp::PartialEq<U>> crate::cmp::PartialEq<[U]> for [T] {
    fn eq(&self, other: &[U]) -> bool {
        if self.len() != other.len() {
            false
        } else {
            let mut res = true;
            for i in 0..self.len() {
                if res && !self[i].eq(&other[i]) {
                    // This should be an early return, but aeneas doesn't support that
                    res = false;
                }
            }
            res
        }
    }
}

#[hax_lib::attributes]
impl<T: crate::cmp::Eq> crate::cmp::Eq for [T] {}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<T: crate::cmp::PartialOrd<T>> crate::cmp::PartialOrd<[T]> for [T] {
    fn partial_cmp(&self, other: &[T]) -> crate::option::Option<crate::cmp::Ordering> {
        // Lexicographic order: compare elements pairwise up to the shorter
        // length; the first non-`Equal` result (including `None`) decides.
        let l = if self.len() < other.len() {
            self.len()
        } else {
            other.len()
        };
        for i in 0..l {
            match self[i].partial_cmp(&other[i]) {
                crate::option::Option::Some(crate::cmp::Ordering::Equal) => (),
                non_eq => return non_eq,
            }
        }
        // All common elements are equal: the shorter slice is smaller.
        if self.len() < other.len() {
            crate::option::Option::Some(crate::cmp::Ordering::Less)
        } else if self.len() > other.len() {
            crate::option::Option::Some(crate::cmp::Ordering::Greater)
        } else {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<T: crate::cmp::Ord> crate::cmp::Ord for [T] {
    fn cmp(&self, other: &[T]) -> crate::cmp::Ordering {
        // Lexicographic order: compare elements pairwise up to the shorter
        // length; the first non-`Equal` result decides.
        let l = if self.len() < other.len() {
            self.len()
        } else {
            other.len()
        };
        for i in 0..l {
            match self[i].cmp(&other[i]) {
                crate::cmp::Ordering::Equal => (),
                non_eq => return non_eq,
            }
        }
        // All common elements are equal: the shorter slice is smaller.
        if self.len() < other.len() {
            crate::cmp::Ordering::Less
        } else if self.len() > other.len() {
            crate::cmp::Ordering::Greater
        } else {
            crate::cmp::Ordering::Equal
        }
    }
}

// aeneas/lean copies of `starts_with`/`ends_with`: they compare with `==`, so
// they sit after the `PartialEq for [T]` impl (source order avoids a forward
// reference to `eq`). Also defined in the F* `impl__` block above.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T> Slice<T> {
    /// See [`std::slice::starts_with`]
    // opaque: slice equality requires eqtype in F*, but T is extracted as Type0
    #[hax_lib::opaque]
    fn starts_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        Self::len(s) >= n && slice_slice(s, 0, n) == needle
    }
    /// See [`std::slice::ends_with`]
    // opaque: slice equality requires eqtype in F*, but T is extracted as Type0
    #[hax_lib::opaque]
    fn ends_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        let l = Self::len(s);
        l >= n && slice_slice(s, l - n, l) == needle
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<'a, T> crate::iter::traits::collect::IntoIterator for &'a [T] {
    type Item = &'a T;
    type IntoIter = iter::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Slice::iter(self)
    }
}
use crate::option::Option;
use rust_primitives::slice::*;

/// `slice::index` follows std's layout: the `SliceIndex` trait and its
/// `usize`/`Range*` impls live in this submodule, and the parent
/// `slice` module re-exports the trait below for backward compat.
/// See [`std::slice::index`].
pub mod index {
    use super::Option;
    use rust_primitives::slice::*;

    /// See [`std::slice::SliceIndex`]. `get_unchecked` is the same in-bounds
    /// projection as `index` (no raw pointers); the `*_mut` variants take
    /// `&mut T` and return `&mut Output`.
    #[hax_lib::attributes]
    pub trait SliceIndex<T: ?Sized> {
        type Output: ?Sized;

        #[hax_lib::requires(true)]
        fn get(self, slice: &T) -> Option<&Self::Output>;

        fn index(self, slice: &T) -> &Self::Output;

        /// See [`std::slice::SliceIndex::get_unchecked`]. In-bounds precondition per impl.
        fn get_unchecked(self, slice: &T) -> &Self::Output;

        // `&mut` returns are unsupported in the F* backend.
        /// See [`std::slice::SliceIndex::get_mut`]. Total, like `get`.
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::requires(true)]
        fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

        /// See [`std::slice::SliceIndex::get_unchecked_mut`]. In-bounds precondition per impl.
        #[cfg(not(hax_backend_fstar))]
        fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;
    }

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T> SliceIndex<[T]> for usize {
        type Output = T;
        fn get(self, slice: &[T]) -> Option<&T> {
            if self < slice_length(slice) {
                Option::Some(slice_index(slice, self))
            } else {
                Option::None
            }
        }
        #[hax_lib::requires(self < slice_length(slice))]
        fn index(self, slice: &[T]) -> &T {
            slice_index(slice, self)
        }
        #[hax_lib::requires(self < slice_length(slice))]
        fn get_unchecked(self, slice: &[T]) -> &T {
            slice_index(slice, self)
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
            if self < slice_length(slice) {
                Option::Some(slice_index_mut(slice, self))
            } else {
                Option::None
            }
        }
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::requires(self < slice_length(slice))]
        fn get_unchecked_mut(self, slice: &mut [T]) -> &mut T {
            slice_index_mut(slice, self)
        }
    }

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T> SliceIndex<[T]> for crate::ops::range::RangeFull {
        type Output = [T];
        fn get(self, slice: &[T]) -> Option<&[T]> {
            Option::Some(slice)
        }
        fn index(self, slice: &[T]) -> &[T] {
            slice
        }
        fn get_unchecked(self, slice: &[T]) -> &[T] {
            slice
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
            Option::Some(slice)
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
            slice
        }
    }

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T> SliceIndex<[T]> for crate::ops::range::RangeFrom<usize> {
        type Output = [T];
        fn get(self, slice: &[T]) -> Option<&[T]> {
            if self.start <= slice_length(slice) {
                Option::Some(slice_slice(slice, self.start, slice_length(slice)))
            } else {
                Option::None
            }
        }
        #[hax_lib::requires(self.start <= slice_length(slice))]
        fn index(self, slice: &[T]) -> &[T] {
            slice_slice(slice, self.start, slice_length(slice))
        }
        #[hax_lib::requires(self.start <= slice_length(slice))]
        fn get_unchecked(self, slice: &[T]) -> &[T] {
            slice_slice(slice, self.start, slice_length(slice))
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
            let len = slice_length(slice);
            if self.start <= len {
                Option::Some(slice_slice_mut(slice, self.start, len))
            } else {
                Option::None
            }
        }
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::requires(self.start <= slice_length(slice))]
        fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
            let len = slice_length(slice);
            slice_slice_mut(slice, self.start, len)
        }
    }
    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T> SliceIndex<[T]> for crate::ops::range::RangeTo<usize> {
        type Output = [T];
        fn get(self, slice: &[T]) -> Option<&[T]> {
            if self.end <= slice_length(slice) {
                Option::Some(slice_slice(slice, 0, self.end))
            } else {
                Option::None
            }
        }
        #[hax_lib::requires(self.end <= slice_length(slice))]
        fn index(self, slice: &[T]) -> &[T] {
            slice_slice(slice, 0, self.end)
        }
        #[hax_lib::requires(self.end <= slice_length(slice))]
        fn get_unchecked(self, slice: &[T]) -> &[T] {
            slice_slice(slice, 0, self.end)
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
            if self.end <= slice_length(slice) {
                Option::Some(slice_slice_mut(slice, 0, self.end))
            } else {
                Option::None
            }
        }
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::requires(self.end <= slice_length(slice))]
        fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
            slice_slice_mut(slice, 0, self.end)
        }
    }
    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T> SliceIndex<[T]> for crate::ops::range::Range<usize> {
        type Output = [T];
        fn get(self, slice: &[T]) -> Option<&[T]> {
            if self.start <= self.end && self.end <= slice_length(slice) {
                Option::Some(slice_slice(slice, self.start, self.end))
            } else {
                Option::None
            }
        }
        #[hax_lib::requires(self.start <= self.end && self.end <= slice_length(slice))]
        fn index(self, slice: &[T]) -> &[T] {
            slice_slice(slice, self.start, self.end)
        }
        #[hax_lib::requires(self.start <= self.end && self.end <= slice_length(slice))]
        fn get_unchecked(self, slice: &[T]) -> &[T] {
            slice_slice(slice, self.start, self.end)
        }
        #[cfg(not(hax_backend_fstar))]
        fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
            if self.start <= self.end && self.end <= slice_length(slice) {
                Option::Some(slice_slice_mut(slice, self.start, self.end))
            } else {
                Option::None
            }
        }
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::requires(self.start <= self.end && self.end <= slice_length(slice))]
        fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
            slice_slice_mut(slice, self.start, self.end)
        }
    }

    /// Generic `Index<I>` for `[T]`, matching std's
    /// `impl<T, I: SliceIndex<[T]>> Index<I> for [T]`
    /// in `core/src/slice/index.rs`. Body delegates to
    /// `SliceIndex::get` (we removed the `index`/`index_mut` methods
    /// from the trait to avoid modeling raw pointers; std would call
    /// `index.index(self)` instead).
    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T, I> crate::ops::index::Index<I> for [T]
    where
        I: SliceIndex<[T]>,
    {
        type Output = I::Output;
        #[hax_lib::requires(i.get(self).is_some())]
        fn index(&self, i: I) -> &I::Output {
            match i.get(self) {
                Option::Some(r) => r,
                Option::None => crate::panicking::internal::panic(),
            }
        }
    }
}

pub use index::SliceIndex;

use crate::ops::{
    index::Index,
    range::{Range, RangeFrom, RangeFull, RangeTo},
};

#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T> Index<Range<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= i.end && i.end <= slice_length(self))]
    fn index(&self, i: Range<usize>) -> &[T] {
        slice_slice(self, i.start, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T> Index<RangeTo<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.end <= slice_length(self))]
    fn index(&self, i: RangeTo<usize>) -> &[T] {
        slice_slice(self, 0, i.end)
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T> Index<RangeFrom<usize>> for &[T] {
    type Output = [T];
    #[hax_lib::requires(i.start <= slice_length(self))]
    fn index(&self, i: RangeFrom<usize>) -> &[T] {
        slice_slice(self, i.start, slice_length(self))
    }
}
#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T> Index<RangeFull> for &[T] {
    type Output = [T];
    fn index(&self, i: RangeFull) -> &[T] {
        slice_slice(self, 0, slice_length(self))
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T> crate::ops::index::Index<usize> for &[T] {
    type Output = T;
    #[hax_lib::requires(i < slice_length(self))]
    fn index(&self, i: usize) -> &T {
        rust_primitives::slice::slice_index(self, i)
    }
}

/// `PartialEq<[U; N]> for [T]` — comparing a slice to an array (`s == [..]`),
/// mirroring std's `impl PartialEq<[U; N]> for [T]`.
pub mod equality {
    use rust_primitives::slice::{array_index, slice_index, slice_length};

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<T: crate::cmp::PartialEq<U>, U, const N: usize> crate::cmp::PartialEq<[U; N]> for [T] {
        fn eq(&self, other: &[U; N]) -> bool {
            if slice_length(self) != N {
                false
            } else {
                let mut res = true;
                for i in 0..N {
                    if res && !slice_index(self, i).eq(array_index(other, i)) {
                        // This should be an early return, but aeneas doesn't support that
                        res = false;
                    }
                }
                res
            }
        }
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
        fn test_first(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(
                Slice::first(&slice[..]).map(|v: &u8| *v),
                slice.first().copied().inject()
            );
        }

        #[test]
        fn test_last(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(
                Slice::last(&slice[..]).map(|v: &u8| *v),
                slice.last().copied().inject()
            );
        }

        #[test]
        fn test_swap(slice in prop::collection::vec(any::<u8>(), 2..=10)) {
            let a = 0;
            let b = slice.len() - 1;
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::swap(&mut model[..], a, b);
            std_slice.swap(a, b);
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_reverse(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::reverse(&mut model[..]);
            std_slice.reverse();
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_starts_with(slice in prop::collection::vec(any::<u8>(), 0..=10), n in 0usize..=10) {
            let n = n.min(slice.len());
            let needle = &slice[..n];
            prop_assert_eq!(Slice::starts_with(&slice[..], needle), slice.starts_with(needle));
        }

        #[test]
        fn test_starts_with_false(slice in prop::collection::vec(any::<u8>(), 1..=10), needle in prop::collection::vec(any::<u8>(), 1..=5)) {
            prop_assert_eq!(Slice::starts_with(&slice[..], &needle[..]), slice.starts_with(&needle[..]));
        }

        #[test]
        fn test_ends_with(slice in prop::collection::vec(any::<u8>(), 0..=10), n in 0usize..=10) {
            let n = n.min(slice.len());
            let needle = &slice[slice.len() - n..];
            prop_assert_eq!(Slice::ends_with(&slice[..], needle), slice.ends_with(needle));
        }

        #[test]
        fn test_ends_with_false(slice in prop::collection::vec(any::<u8>(), 1..=10), needle in prop::collection::vec(any::<u8>(), 1..=5)) {
            prop_assert_eq!(Slice::ends_with(&slice[..], &needle[..]), slice.ends_with(&needle[..]));
        }

        #[test]
        fn test_fill(value in any::<u8>(), len in 1usize..=10) {
            let mut model = vec![0u8; len];
            let mut std_slice = vec![0u8; len];
            Slice::fill(&mut model[..], value);
            std_slice.fill(value);
            prop_assert_eq!(model, std_slice);
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

        // ----- PartialEq / PartialOrd / Ord (lexicographic) ------------------

        #[test]
        fn test_slice_eq(
            a in prop::collection::vec(any::<u8>(), 0..=8),
            b in prop::collection::vec(any::<u8>(), 0..=8),
        ) {
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialEq<[u8]>>::eq(&a[..], &b[..]),
                a == b
            );
        }

        // Equal-length pairs make the per-element comparison the deciding factor
        // more often than two independent (usually different-length) slices.
        #[test]
        fn test_slice_eq_same_len(pairs in prop::collection::vec((any::<u8>(), any::<u8>()), 0..=8)) {
            let a: Vec<u8> = pairs.iter().map(|p| p.0).collect();
            let b: Vec<u8> = pairs.iter().map(|p| p.1).collect();
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialEq<[u8]>>::eq(&a[..], &b[..]),
                a == b
            );
        }

        #[test]
        fn test_slice_partial_cmp(
            a in prop::collection::vec(any::<u8>(), 0..=8),
            b in prop::collection::vec(any::<u8>(), 0..=8),
        ) {
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialOrd<[u8]>>::partial_cmp(&a[..], &b[..]),
                a[..].partial_cmp(&b[..]).inject()
            );
        }

        #[test]
        fn test_slice_cmp(
            a in prop::collection::vec(any::<u8>(), 0..=8),
            b in prop::collection::vec(any::<u8>(), 0..=8),
        ) {
            prop_assert_eq!(
                <[u8] as crate::cmp::Ord>::cmp(&a[..], &b[..]),
                a[..].cmp(&b[..]).inject()
            );
        }

        // `[T]: PartialEq<[U; N]>` — slice vs array (`s == [..]`). `use_equal`
        // biases toward the equal case, which random slices rarely hit.
        #[test]
        fn test_eq_array(
            arr in any::<[u8; 3]>(),
            other in prop::collection::vec(any::<u8>(), 0..=6),
            use_equal in any::<bool>(),
        ) {
            let v: Vec<u8> = if use_equal { arr.to_vec() } else { other };
            let s: &[u8] = &v[..];
            let model = <[u8] as crate::cmp::PartialEq<[u8; 3]>>::eq(s, &arr);
            let std_eq = s == arr;
            prop_assert_eq!(model, std_eq);
        }

        // ----- get_unchecked (in-bounds) -------------------------------------

        #[test]
        fn test_get_unchecked_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(Slice::get_unchecked(s, idx), unsafe { s.get_unchecked(idx) });
        }

        #[test]
        fn test_get_unchecked_range(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..8, len in 0usize..8) {
            let end = (start + len).min(8);
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                Slice::get_unchecked(s, crate::ops::range::Range { start, end }),
                unsafe { s.get_unchecked(start..end) }
            );
        }

        #[test]
        fn test_get_unchecked_range_from(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..=8) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                Slice::get_unchecked(s, crate::ops::range::RangeFrom { start }),
                unsafe { s.get_unchecked(start..) }
            );
        }

        #[test]
        fn test_get_unchecked_range_to(slice in prop::collection::vec(any::<u8>(), 8..=8), end in 0usize..=8) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                Slice::get_unchecked(s, crate::ops::range::RangeTo { end }),
                unsafe { s.get_unchecked(..end) }
            );
        }

        #[test]
        fn test_get_unchecked_range_full(slice in prop::collection::vec(any::<u8>(), 0..=8)) {
            let s: &[u8] = &slice[..];
            prop_assert_eq!(
                Slice::get_unchecked(s, crate::ops::range::RangeFull),
                unsafe { s.get_unchecked(..) }
            );
        }

        // ----- get_mut / get_unchecked_mut (mutate through the &mut) ---------

        #[test]
        fn test_get_mut_usize(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in any::<usize>(), v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let crate::option::Option::Some(r) = Slice::get_mut(&mut model[..], idx) {
                *r = v;
            }
            if let Some(r) = std_slice.get_mut(idx) {
                *r = v;
            }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_mut_range(slice in prop::collection::vec(any::<u8>(), 1..=10), start in 0usize..10, end in 0usize..10, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let crate::option::Option::Some(r) = Slice::get_mut(&mut model[..], crate::ops::range::Range { start, end }) {
                r.fill(v);
            }
            if let Some(r) = std_slice.get_mut(start..end) {
                r.fill(v);
            }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_mut_range_from(slice in prop::collection::vec(any::<u8>(), 1..=10), start in 0usize..=10, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let crate::option::Option::Some(r) = Slice::get_mut(&mut model[..], crate::ops::range::RangeFrom { start }) {
                r.fill(v);
            }
            if let Some(r) = std_slice.get_mut(start..) {
                r.fill(v);
            }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_mut_range_to(slice in prop::collection::vec(any::<u8>(), 1..=10), end in 0usize..=10, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let crate::option::Option::Some(r) = Slice::get_mut(&mut model[..], crate::ops::range::RangeTo { end }) {
                r.fill(v);
            }
            if let Some(r) = std_slice.get_mut(..end) {
                r.fill(v);
            }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_mut_range_full(slice in prop::collection::vec(any::<u8>(), 0..=10), v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let crate::option::Option::Some(r) = Slice::get_mut(&mut model[..], crate::ops::range::RangeFull) {
                r.fill(v);
            }
            if let Some(r) = std_slice.get_mut(..) {
                r.fill(v);
            }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_unchecked_mut_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            *Slice::get_unchecked_mut(&mut model[..], idx) = v;
            unsafe { *std_slice.get_unchecked_mut(idx) = v; }
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_get_unchecked_mut_range(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..8, len in 0usize..8, v in any::<u8>()) {
            let end = (start + len).min(8);
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::get_unchecked_mut(&mut model[..], crate::ops::range::Range { start, end }).fill(v);
            unsafe { std_slice.get_unchecked_mut(start..end).fill(v); }
            prop_assert_eq!(model, std_slice);
        }
    }
}
