use crate::result::Result;

// Dummy type to allow impls
// F*-only: `charon::exclude` would drop this dummy type while its `impl`
// blocks still reference it (see f32.rs).
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct Slice<T>([T]);

pub mod iter {
    use crate::option::Option;
    use rust_primitives::{sequence::*, slice::*};

    /// Index of the first element of `s` satisfying `pred`, or `s.len()` if
    /// there is none. A bounded loop with no early exit, which is the shape both
    /// backends handle; `pred` is taken by reference so the split iterators can
    /// call it out of `&mut self`.
    // F*-only: applying a `Fn` bound in F* leaves the result at the trait's
    // abstract `Output` type rather than `bool`, and there the `ensures` is the
    // only thing callers need out of the body. `charon::opaque` would drop the
    // Lean declaration, so the Lean lane takes the body.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::ensures(|res| res <= slice_length(s))]
    pub(super) fn position_of<T, P: Fn(&T) -> bool>(s: &[T], pred: &P) -> usize {
        let len = slice_length(s);
        let mut res = len;
        for i in 0..len {
            if res == len && (*pred)(slice_index(s, i)) {
                res = i;
            }
        }
        res
    }

    /// Index of the *last* element of `s` satisfying `pred`, or `s.len()` if
    /// there is none.
    // F*-only: see `position_of`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::ensures(|res| res <= slice_length(s))]
    pub(super) fn rposition_of<T, P: Fn(&T) -> bool>(s: &[T], pred: &P) -> usize {
        let len = slice_length(s);
        let mut res = len;
        for i in 0..len {
            if (*pred)(slice_index(s, i)) {
                res = i;
            }
        }
        res
    }

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
        rem: &'a [T],
    }
    impl<'a, T> ChunksExact<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> ChunksExact<'a, T> {
            let len = slice_length(elements);
            // `cs == 0` is unreachable (`Slice::chunks_exact` panics on it), but
            // the guard is what lets the backends discharge the division.
            let rem_len = if cs == 0 { 0 } else { len % cs };
            let rem = slice_slice(elements, len - rem_len, len);
            ChunksExact { cs, elements, rem }
        }
        /// See [`std::slice::ChunksExact::remainder`]
        pub fn remainder(&self) -> &'a [T] {
            self.rem
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
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
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

    // ------------------------------------------------------------------------
    // Everything below is a later addition, and every `impl` here carries
    // `#[hax_lib::attributes]` on purpose. hax numbers the `impl` blocks of a
    // module by putting the plain ones first and the ones carrying a `hax_lib`
    // attribute after them (hax#828), so an *attributed* block appended at the
    // end of the module is the only kind that does not renumber — and rename —
    // the `impl__*` definitions above in the F* output.
    // ------------------------------------------------------------------------

    /// See [`std::slice::RChunks`]
    pub struct RChunks<'a, T> {
        cs: usize,
        elements: &'a [T],
    }
    #[hax_lib::attributes]
    impl<'a, T> RChunks<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> RChunks<'a, T> {
            RChunks { cs, elements }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T> crate::iter::traits::iterator::Iterator for RChunks<'a, T> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            let len = slice_length(self.elements);
            if len == 0 {
                Option::None
            } else if len < self.cs {
                let res = self.elements;
                self.elements = slice_slice(self.elements, 0, 0);
                Option::Some(res)
            } else {
                let (rest, res) = slice_split_at(self.elements, len - self.cs);
                self.elements = rest;
                Option::Some(res)
            }
        }
    }

    /// See [`std::slice::RChunksExact`]
    pub struct RChunksExact<'a, T> {
        cs: usize,
        elements: &'a [T],
        rem: &'a [T],
    }
    #[hax_lib::attributes]
    impl<'a, T> RChunksExact<'a, T> {
        pub fn new(cs: usize, elements: &'a [T]) -> RChunksExact<'a, T> {
            // Unlike `ChunksExact`, the elements the iterator never reaches sit
            // at the *front*. `cs == 0` is guarded as in `ChunksExact::new`.
            let rem_len = if cs == 0 {
                0
            } else {
                slice_length(elements) % cs
            };
            let (rem, els) = slice_split_at(elements, rem_len);
            RChunksExact {
                cs,
                elements: els,
                rem,
            }
        }
        /// See [`std::slice::RChunksExact::remainder`]
        pub fn remainder(&self) -> &'a [T] {
            self.rem
        }
    }

    #[hax_lib::attributes]
    impl<'a, T> crate::iter::traits::iterator::Iterator for RChunksExact<'a, T> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            let len = slice_length(self.elements);
            if len < self.cs {
                Option::None
            } else {
                let (rest, res) = slice_split_at(self.elements, len - self.cs);
                self.elements = rest;
                Option::Some(res)
            }
        }
    }

    /// See [`std::slice::Split`]
    pub struct Split<'a, T, P> {
        v: &'a [T],
        pred: P,
        finished: bool,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> Split<'a, T, P> {
        pub fn new(v: &'a [T], pred: P) -> Split<'a, T, P> {
            Split {
                v,
                pred,
                finished: false,
            }
        }
        /// See [`std::slice::Split::as_slice`]
        pub fn as_slice(&self) -> &'a [T] {
            if self.finished {
                slice_slice(self.v, 0, 0)
            } else {
                self.v
            }
        }
        /// Yields the whole remaining slice and stops: what `splitn` does once
        /// its split budget is used up.
        pub(super) fn finish(&mut self) -> Option<&'a [T]> {
            if self.finished {
                Option::None
            } else {
                self.finished = true;
                Option::Some(self.v)
            }
        }
        /// The `DoubleEndedIterator` half of `Split`, which is all `RSplit` is.
        pub(super) fn next_back(&mut self) -> Option<&'a [T]> {
            if self.finished {
                Option::None
            } else {
                let len = slice_length(self.v);
                let idx = rposition_of(self.v, &self.pred);
                if idx == len {
                    self.finished = true;
                    Option::Some(self.v)
                } else {
                    let res = slice_slice(self.v, idx + 1, len);
                    self.v = slice_slice(self.v, 0, idx);
                    Option::Some(res)
                }
            }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> crate::iter::traits::iterator::Iterator for Split<'a, T, P> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if self.finished {
                Option::None
            } else {
                let len = slice_length(self.v);
                let idx = position_of(self.v, &self.pred);
                if idx == len {
                    self.finished = true;
                    Option::Some(self.v)
                } else {
                    let res = slice_slice(self.v, 0, idx);
                    self.v = slice_slice(self.v, idx + 1, len);
                    Option::Some(res)
                }
            }
        }
    }

    /// See [`std::slice::SplitInclusive`]
    pub struct SplitInclusive<'a, T, P> {
        v: &'a [T],
        pred: P,
        finished: bool,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> SplitInclusive<'a, T, P> {
        pub fn new(v: &'a [T], pred: P) -> SplitInclusive<'a, T, P> {
            // The empty slice yields nothing at all, not one empty subslice.
            let finished = slice_length(v) == 0;
            SplitInclusive { v, pred, finished }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> crate::iter::traits::iterator::Iterator
        for SplitInclusive<'a, T, P>
    {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if self.finished {
                Option::None
            } else {
                let len = slice_length(self.v);
                let p = position_of(self.v, &self.pred);
                // The matched element terminates the subslice instead of being
                // dropped, so the cut sits one past it.
                let idx = if p == len { len } else { p + 1 };
                if idx == len {
                    self.finished = true;
                }
                let res = slice_slice(self.v, 0, idx);
                self.v = slice_slice(self.v, idx, len);
                Option::Some(res)
            }
        }
    }

    /// See [`std::slice::SplitN`]
    pub struct SplitN<'a, T, P> {
        inner: Split<'a, T, P>,
        count: usize,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> SplitN<'a, T, P> {
        pub fn new(v: &'a [T], n: usize, pred: P) -> SplitN<'a, T, P> {
            SplitN {
                inner: Split::new(v, pred),
                count: n,
            }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> crate::iter::traits::iterator::Iterator for SplitN<'a, T, P> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 {
                Option::None
            } else if self.count == 1 {
                self.count = 0;
                self.inner.finish()
            } else {
                self.count = self.count - 1;
                crate::iter::traits::iterator::Iterator::next(&mut self.inner)
            }
        }
    }

    /// See [`std::slice::RSplit`]
    pub struct RSplit<'a, T, P> {
        inner: Split<'a, T, P>,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> RSplit<'a, T, P> {
        pub fn new(v: &'a [T], pred: P) -> RSplit<'a, T, P> {
            RSplit {
                inner: Split::new(v, pred),
            }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> crate::iter::traits::iterator::Iterator for RSplit<'a, T, P> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next_back()
        }
    }

    /// See [`std::slice::RSplitN`]
    pub struct RSplitN<'a, T, P> {
        inner: Split<'a, T, P>,
        count: usize,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> RSplitN<'a, T, P> {
        pub fn new(v: &'a [T], n: usize, pred: P) -> RSplitN<'a, T, P> {
            RSplitN {
                inner: Split::new(v, pred),
                count: n,
            }
        }
    }

    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T) -> bool> crate::iter::traits::iterator::Iterator for RSplitN<'a, T, P> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            if self.count == 0 {
                Option::None
            } else if self.count == 1 {
                self.count = 0;
                self.inner.finish()
            } else {
                self.count = self.count - 1;
                self.inner.next_back()
            }
        }
    }

    /// See [`std::slice::ChunkBy`]
    pub struct ChunkBy<'a, T, P> {
        v: &'a [T],
        pred: P,
    }
    #[hax_lib::attributes]
    impl<'a, T, P: Fn(&T, &T) -> bool> ChunkBy<'a, T, P> {
        pub fn new(v: &'a [T], pred: P) -> ChunkBy<'a, T, P> {
            ChunkBy { v, pred }
        }
    }

    // opaque: F* gets no bound on the run length `n` out of the loop, so it
    // cannot see that the split below is in range.
    #[hax_lib::opaque]
    impl<'a, T, P: Fn(&T, &T) -> bool> crate::iter::traits::iterator::Iterator for ChunkBy<'a, T, P> {
        type Item = &'a [T];
        fn next(&mut self) -> Option<Self::Item> {
            let len = slice_length(self.v);
            if len == 0 {
                Option::None
            } else {
                // `n == i` is the "the run is still unbroken" guard: once a pair
                // fails the predicate, `n` stops tracking `i` and stays put.
                let mut n = 1;
                for i in 0..len {
                    if i > 0
                        && n == i
                        && (self.pred)(slice_index(self.v, i - 1), slice_index(self.v, i))
                    {
                        n = i + 1;
                    }
                }
                let (res, rest) = slice_split_at(self.v, n);
                self.v = rest;
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
    #[hax_lib::requires(cs > 0)]
    fn chunks<'a>(s: &'a [T], cs: usize) -> iter::Chunks<'a, T> {
        if cs == 0 {
            crate::panicking::internal::panic()
        }
        iter::Chunks::new(cs, s)
    }
    /// See [`std::slice::iter`]
    fn iter(s: &[T]) -> iter::Iter<'_, T> {
        iter::Iter(rust_primitives::sequence::seq_from_slice(s))
    }
    /// See [`std::slice::chunks_exact`]
    #[hax_lib::requires(cs > 0)]
    fn chunks_exact<'a>(s: &'a [T], cs: usize) -> iter::ChunksExact<'a, T> {
        if cs == 0 {
            crate::panicking::internal::panic()
        }
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
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn contains(s: &[T], v: &T) -> bool
    where
        T: PartialEq,
    {
        rust_primitives::slice::slice_contains(s, v)
    }
    /// See [`std::slice::copy_within`]
    // Excluded from coverage: `R` carries no `RangeBounds` bound, so the source
    // range cannot be read out of it and there is no body to run (same
    // limitation as `alloc`'s `Vec::drain`).
    #[cfg_attr(coverage_nightly, coverage(off))]
    #[hax_lib::opaque]
    // mutants::skip: excluded from coverage above, so no test can kill a mutant here.
    #[cfg_attr(test, mutants::skip)]
    fn copy_within<R>(s: &[T], src: R, dest: usize) -> &[T]
    where
        T: Copy,
    {
        panic!()
    }
    /// See [`std::slice::binary_search`]
    // F*-only: the equivalence tests call this, so Lean needs the body; it is
    // written over primitives the Lean library provides.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn binary_search(s: &[T], x: &T) -> Result<usize, usize>
    where
        T: crate::cmp::Ord,
    {
        let mut low = 0;
        let mut high = Self::len(s);
        while low < high {
            let mid = low + (high - low) / 2;
            match crate::cmp::Ord::cmp(rust_primitives::slice::slice_index(s, mid), x) {
                crate::cmp::Ordering::Less => low = mid + 1,
                crate::cmp::Ordering::Greater => high = mid,
                crate::cmp::Ordering::Equal => return Result::Ok(mid),
            }
        }
        Result::Err(low)
    }
    /// See [`std::slice::get`]
    fn get<I: SliceIndex<[T]>>(s: &[T], index: I) -> Option<&<I as SliceIndex<[T]>>::Output> {
        index.get(s)
    }
    /// See [`std::slice::get_unchecked`]
    // opaque for F*: the generic precondition isn't provable here (the concrete
    // `SliceIndex` impls verify).
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[cfg_attr(not(charon), hax_lib::requires(index.get(s).is_some()))]
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
    #[cfg_attr(not(charon), hax_lib::requires(index.get(s).is_some()))]
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
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn fill(s: &mut [T], value: T)
    where
        T: Clone,
    {
        for i in 0..s.len() {
            s[i] = value.clone();
        }
    }
    /// See [`std::slice::fill_with`]
    // F*-only: see `fill`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn fill_with<F: Fn() -> T>(s: &mut [T], f: F) {
        for i in 0..s.len() {
            s[i] = f();
        }
    }
    /// See [`std::slice::as_slice`]
    fn as_slice(s: &[T]) -> &[T] {
        s
    }
    /// See [`std::slice::split_first`]
    fn split_first(s: &[T]) -> Option<(&T, &[T])> {
        if Self::is_empty(s) {
            Option::None
        } else {
            Option::Some((slice_index(s, 0), slice_slice(s, 1, Self::len(s))))
        }
    }
    /// See [`std::slice::split_last`]
    fn split_last(s: &[T]) -> Option<(&T, &[T])> {
        if Self::is_empty(s) {
            Option::None
        } else {
            let l = Self::len(s);
            Option::Some((slice_index(s, l - 1), slice_slice(s, 0, l - 1)))
        }
    }
    /// See [`std::slice::split_at_unchecked`]
    #[hax_lib::requires(mid <= Slice::len(s))]
    fn split_at_unchecked(s: &[T], mid: usize) -> (&[T], &[T]) {
        rust_primitives::slice::slice_split_at(s, mid)
    }
    /// See [`std::slice::swap_unchecked`]
    // opaque for F*: see `swap`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(a < Slice::len(s) && b < Slice::len(s))]
    fn swap_unchecked(s: &mut [T], a: usize, b: usize) {
        rust_primitives::slice::slice_swap(s, a, b);
    }
    /// See [`std::slice::rotate_left`]
    // opaque for F*: see `swap`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(mid <= Slice::len(s))]
    fn rotate_left(s: &mut [T], mid: usize) {
        if mid > Self::len(s) {
            crate::panicking::internal::panic()
        }
        // Rotation as three reversals: it needs no element copies, so it works
        // for a bare `T` (`slice_reverse` is the only in-place primitive that
        // moves elements without a `Clone`/`Copy` bound).
        let len = Self::len(s);
        slice_reverse(slice_slice_mut(s, 0, mid));
        slice_reverse(slice_slice_mut(s, mid, len));
        slice_reverse(s);
    }
    /// See [`std::slice::rotate_right`]
    // opaque for F*: see `swap`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(k <= Slice::len(s))]
    fn rotate_right(s: &mut [T], k: usize) {
        if k > Self::len(s) {
            crate::panicking::internal::panic()
        }
        let len = Self::len(s);
        Self::rotate_left(s, len - k);
    }
    /// See [`std::slice::rchunks`]
    #[hax_lib::requires(cs > 0)]
    fn rchunks<'a>(s: &'a [T], cs: usize) -> iter::RChunks<'a, T> {
        if cs == 0 {
            crate::panicking::internal::panic()
        }
        iter::RChunks::new(cs, s)
    }
    /// See [`std::slice::rchunks_exact`]
    #[hax_lib::requires(cs > 0)]
    fn rchunks_exact<'a>(s: &'a [T], cs: usize) -> iter::RChunksExact<'a, T> {
        if cs == 0 {
            crate::panicking::internal::panic()
        }
        iter::RChunksExact::new(cs, s)
    }
    /// See [`std::slice::split`]
    fn split<'a, P: Fn(&T) -> bool>(s: &'a [T], pred: P) -> iter::Split<'a, T, P> {
        iter::Split::new(s, pred)
    }
    /// See [`std::slice::split_inclusive`]
    fn split_inclusive<'a, P: Fn(&T) -> bool>(
        s: &'a [T],
        pred: P,
    ) -> iter::SplitInclusive<'a, T, P> {
        iter::SplitInclusive::new(s, pred)
    }
    /// See [`std::slice::splitn`]
    fn splitn<'a, P: Fn(&T) -> bool>(s: &'a [T], n: usize, pred: P) -> iter::SplitN<'a, T, P> {
        iter::SplitN::new(s, n, pred)
    }
    /// See [`std::slice::rsplit`]
    fn rsplit<'a, P: Fn(&T) -> bool>(s: &'a [T], pred: P) -> iter::RSplit<'a, T, P> {
        iter::RSplit::new(s, pred)
    }
    /// See [`std::slice::rsplitn`]
    fn rsplitn<'a, P: Fn(&T) -> bool>(s: &'a [T], n: usize, pred: P) -> iter::RSplitN<'a, T, P> {
        iter::RSplitN::new(s, n, pred)
    }
    /// See [`std::slice::chunk_by`]
    fn chunk_by<'a, P: Fn(&T, &T) -> bool>(s: &'a [T], pred: P) -> iter::ChunkBy<'a, T, P> {
        iter::ChunkBy::new(s, pred)
    }
    /// See [`std::slice::split_once`]
    fn split_once<P: Fn(&T) -> bool>(s: &[T], pred: P) -> Option<(&[T], &[T])> {
        let len = Self::len(s);
        let idx = iter::position_of(s, &pred);
        if idx == len {
            Option::None
        } else {
            Option::Some((slice_slice(s, 0, idx), slice_slice(s, idx + 1, len)))
        }
    }
    /// See [`std::slice::rsplit_once`]
    fn rsplit_once<P: Fn(&T) -> bool>(s: &[T], pred: P) -> Option<(&[T], &[T])> {
        let len = Self::len(s);
        let idx = iter::rposition_of(s, &pred);
        if idx == len {
            Option::None
        } else {
            Option::Some((slice_slice(s, 0, idx), slice_slice(s, idx + 1, len)))
        }
    }
    /// See [`std::slice::binary_search_by`]
    // opaque for F*: the loop below has no termination measure there.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn binary_search_by<F: Fn(&T) -> crate::cmp::Ordering>(s: &[T], f: F) -> Result<usize, usize> {
        let len = Self::len(s);
        if len == 0 {
            Result::Err(0)
        } else {
            let mut base = 0;
            let mut size = len;
            // std narrows `size` with a `while size > 1` loop; `size` at least
            // halves every step, so `len` iterations is a safe bound and keeps
            // the loop the bounded shape the backends handle.
            for _i in 0..len {
                if size > 1 {
                    let half = size / 2;
                    let mid = base + half;
                    match f(slice_index(s, mid)) {
                        crate::cmp::Ordering::Greater => (),
                        _ => base = mid,
                    }
                    size = size - half;
                }
            }
            match f(slice_index(s, base)) {
                crate::cmp::Ordering::Equal => Result::Ok(base),
                crate::cmp::Ordering::Less => Result::Err(base + 1),
                crate::cmp::Ordering::Greater => Result::Err(base),
            }
        }
    }
    /// See [`std::slice::binary_search_by_key`]
    // opaque for F*: see `binary_search_by`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn binary_search_by_key<B: crate::cmp::Ord, F: Fn(&T) -> B>(
        s: &[T],
        b: &B,
        f: F,
    ) -> Result<usize, usize> {
        // Spelled out rather than delegating to `binary_search_by` with a
        // closure: building closures inside the model extracts poorly.
        let len = Self::len(s);
        if len == 0 {
            Result::Err(0)
        } else {
            let mut base = 0;
            let mut size = len;
            for _i in 0..len {
                if size > 1 {
                    let half = size / 2;
                    let mid = base + half;
                    match f(slice_index(s, mid)).cmp(b) {
                        crate::cmp::Ordering::Greater => (),
                        _ => base = mid,
                    }
                    size = size - half;
                }
            }
            match f(slice_index(s, base)).cmp(b) {
                crate::cmp::Ordering::Equal => Result::Ok(base),
                crate::cmp::Ordering::Less => Result::Err(base + 1),
                crate::cmp::Ordering::Greater => Result::Err(base),
            }
        }
    }
    /// See [`std::slice::partition_point`]
    // opaque for F*: see `binary_search_by`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn partition_point<P: Fn(&T) -> bool>(s: &[T], pred: P) -> usize {
        // The same search as `binary_search_by` with `pred` mapped to
        // `Less`/`Greater`, spelled out to avoid building a closure.
        let len = Self::len(s);
        if len == 0 {
            0
        } else {
            let mut base = 0;
            let mut size = len;
            for _i in 0..len {
                if size > 1 {
                    let half = size / 2;
                    let mid = base + half;
                    if pred(slice_index(s, mid)) {
                        base = mid;
                    }
                    size = size - half;
                }
            }
            if pred(slice_index(s, base)) {
                base + 1
            } else {
                base
            }
        }
    }
    /// See [`std::slice::is_sorted`]
    // opaque for F*: bounded loop over the slice.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn is_sorted(s: &[T]) -> bool
    where
        T: crate::cmp::PartialOrd<T>,
    {
        let mut res = true;
        for i in 0..Self::len(s) {
            if i > 0 {
                match slice_index(s, i - 1).partial_cmp(slice_index(s, i)) {
                    Option::Some(crate::cmp::Ordering::Less) => (),
                    Option::Some(crate::cmp::Ordering::Equal) => (),
                    // Incomparable elements (`None`) are not sorted either.
                    _ => res = false,
                }
            }
        }
        res
    }
    /// See [`std::slice::is_sorted_by`]
    // opaque for F*: see `is_sorted`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn is_sorted_by<F: Fn(&T, &T) -> bool>(s: &[T], compare: F) -> bool {
        let mut res = true;
        for i in 0..Self::len(s) {
            if i > 0 && !compare(slice_index(s, i - 1), slice_index(s, i)) {
                res = false;
            }
        }
        res
    }
    /// See [`std::slice::is_sorted_by_key`]
    // opaque for F*: see `is_sorted`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn is_sorted_by_key<K: crate::cmp::PartialOrd<K>, F: Fn(&T) -> K>(s: &[T], f: F) -> bool {
        let mut res = true;
        for i in 0..Self::len(s) {
            if i > 0 {
                let a = f(slice_index(s, i - 1));
                let b = f(slice_index(s, i));
                match a.partial_cmp(&b) {
                    Option::Some(crate::cmp::Ordering::Less) => (),
                    Option::Some(crate::cmp::Ordering::Equal) => (),
                    _ => res = false,
                }
            }
        }
        res
    }
    // `&mut` returns are unsupported in the F* backend.
    /// See [`std::slice::as_mut_slice`]
    #[cfg(not(hax_backend_fstar))]
    fn as_mut_slice(s: &mut [T]) -> &mut [T] {
        s
    }
    /// See [`std::slice::first_mut`]
    #[cfg(not(hax_backend_fstar))]
    fn first_mut(s: &mut [T]) -> Option<&mut T> {
        if Self::is_empty(s) {
            Option::None
        } else {
            Option::Some(slice_index_mut(s, 0))
        }
    }
    /// See [`std::slice::last_mut`]
    #[cfg(not(hax_backend_fstar))]
    fn last_mut(s: &mut [T]) -> Option<&mut T> {
        if Self::is_empty(s) {
            Option::None
        } else {
            let l = Self::len(s);
            Option::Some(slice_index_mut(s, l - 1))
        }
    }
    // `split_off_first`/`split_off_last` retarget the *caller's* `&[T]`, so they
    // take `&mut &[T]`; the F* backend has no model for that.
    /// See [`std::slice::split_off_first`]
    #[cfg(not(hax_backend_fstar))]
    fn split_off_first<'a>(s: &mut &'a [T]) -> Option<&'a T> {
        let len = slice_length(*s);
        if len == 0 {
            Option::None
        } else {
            let first = slice_index(*s, 0);
            *s = slice_slice(*s, 1, len);
            Option::Some(first)
        }
    }
    /// See [`std::slice::split_off_last`]
    #[cfg(not(hax_backend_fstar))]
    fn split_off_last<'a>(s: &mut &'a [T]) -> Option<&'a T> {
        let len = slice_length(*s);
        if len == 0 {
            Option::None
        } else {
            let last = slice_index(*s, len - 1);
            *s = slice_slice(*s, 0, len - 1);
            Option::Some(last)
        }
    }

    // F* names inherent methods by impl-block order, so `starts_with`/`ends_with`
    // live in this first block (as opaque vals) for F* to keep their `impl__`
    // name. The aeneas/lean copies are in the `cfg(not(hax_backend_fstar))` block
    // after the `PartialEq for [T]` impl, where source order avoids a forward
    // reference to `eq`.
    /// See [`std::slice::starts_with`]
    #[cfg(hax_backend_fstar)]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn starts_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        Self::len(s) >= n && slice_slice(s, 0, n) == needle
    }
    /// See [`std::slice::ends_with`]
    #[cfg(hax_backend_fstar)]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
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
    #[cfg(not(hax_backend_fstar))]
    fn ne(&self, other: &[U]) -> bool {
        self.eq(other) == false
    }
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
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn starts_with(s: &[T], needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = Self::len(needle);
        Self::len(s) >= n && slice_slice(s, 0, n) == needle
    }
    /// See [`std::slice::ends_with`]
    // opaque: slice equality requires eqtype in F*, but T is extracted as Type0
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
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
        #[cfg_attr(not(charon), hax_lib::requires(i.get(self).is_some()))]
        fn index(&self, i: I) -> &I::Output {
            match i.get(self) {
                Option::Some(r) => r,
                Option::None => crate::panicking::internal::panic(),
            }
        }
    }

    /// Generic `IndexMut<I>` for `[T]`, mirroring the `Index<I>` impl above and
    /// std's `impl<T, I: SliceIndex<[T]>> IndexMut<I> for [T]`. Delegates to
    /// `SliceIndex::get_mut` (Lean-only, as the mutable accessors are).
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
    impl<T, I> crate::ops::index::IndexMut<I> for [T]
    where
        I: SliceIndex<[T]>,
    {
        // `get_unchecked_mut` (not a `get_mut` + panicking `match`): a panic in
        // the `None` arm would have to produce the `&mut` return, which aeneas
        // lowers to a `(value, write-back)` pair and cannot synthesise from a
        // divergent `panic`. The precondition mirrors `Index::index`.
        // Kept out of the Lean lane: routed through hax's spec channel, this
        // precondition makes aeneas fail with an internal `Invalid_argument`.
        #[cfg_attr(not(charon), hax_lib::requires(i.get(self).is_some()))]
        fn index_mut(&mut self, i: I) -> &mut I::Output {
            i.get_unchecked_mut(self)
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
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &[U; N]) -> bool {
            self.eq(other) == false
        }
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

// `SlicePattern` and the `strip_*`/`trim_*` methods it serves. Two placement
// constraints meet here:
//   * they decide with `starts_with`/`ends_with`, so they must follow *both*
//     definitions of those in source order — that is what the Lean extraction
//     resolves against;
//   * hax numbers a module's `impl` blocks with the plain ones first and the
//     ones carrying a `hax_lib` attribute after them (hax#828), so only an
//     *attributed* block appended at the end of the module avoids renumbering —
//     and renaming — every `impl__*` above in the F* output. Hence the
//     `#[hax_lib::attributes]` on blocks that declare no contract.
/// See [`std::slice::SlicePattern`]
pub trait SlicePattern {
    /// See [`std::slice::SlicePattern::Item`]
    type Item;
    /// See [`std::slice::SlicePattern::as_slice`]
    fn as_slice(&self) -> &[Self::Item];
}

#[hax_lib::attributes]
impl<T> SlicePattern for [T] {
    type Item = T;
    fn as_slice(&self) -> &[T] {
        self
    }
}

#[hax_lib::attributes]
impl<T, const N: usize> SlicePattern for [T; N] {
    type Item = T;
    fn as_slice(&self) -> &[T] {
        array_as_slice(self)
    }
}

#[hax_lib::attributes]
impl<T> Slice<T> {
    /// See [`std::slice::strip_prefix`]
    // opaque for F*: the subslice bound follows from `starts_with`, which is
    // itself opaque there and so carries no postcondition.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn strip_prefix<'a, P: SlicePattern<Item = T> + ?Sized>(
        s: &'a [T],
        prefix: &P,
    ) -> Option<&'a [T]>
    where
        T: PartialEq,
    {
        let p = prefix.as_slice();
        if Self::starts_with(s, p) {
            Option::Some(slice_slice(s, Self::len(p), Self::len(s)))
        } else {
            Option::None
        }
    }
    /// See [`std::slice::strip_suffix`]
    // opaque for F*: see `strip_prefix`.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn strip_suffix<'a, P: SlicePattern<Item = T> + ?Sized>(
        s: &'a [T],
        suffix: &P,
    ) -> Option<&'a [T]>
    where
        T: PartialEq,
    {
        let p = suffix.as_slice();
        if Self::ends_with(s, p) {
            Option::Some(slice_slice(s, 0, Self::len(s) - Self::len(p)))
        } else {
            Option::None
        }
    }
    /// See [`std::slice::trim_prefix`]
    fn trim_prefix<'a, P: SlicePattern<Item = T> + ?Sized>(s: &'a [T], prefix: &P) -> &'a [T]
    where
        T: PartialEq,
    {
        match Self::strip_prefix(s, prefix) {
            Option::Some(rest) => rest,
            Option::None => s,
        }
    }
    /// See [`std::slice::trim_suffix`]
    fn trim_suffix<'a, P: SlicePattern<Item = T> + ?Sized>(s: &'a [T], suffix: &P) -> &'a [T]
    where
        T: PartialEq,
    {
        match Self::strip_suffix(s, suffix) {
            Option::Some(rest) => rest,
            Option::None => s,
        }
    }
    /// See [`std::slice::strip_circumfix`]
    fn strip_circumfix<'a, S, P>(s: &'a [T], prefix: &P, suffix: &S) -> Option<&'a [T]>
    where
        T: PartialEq,
        S: SlicePattern<Item = T> + ?Sized,
        P: SlicePattern<Item = T> + ?Sized,
    {
        match Self::strip_prefix(s, prefix) {
            Option::Some(rest) => Self::strip_suffix(rest, suffix),
            Option::None => Option::None,
        }
    }
}

/// `slice::ascii` mirrors `core`'s own `slice/ascii.rs`: the ASCII helpers are
/// `[u8]`-specific, so they hang off `Slice<u8>` rather than the generic block.
/// The module path has to match `core`'s, because that is what the Lean
/// extraction of a `[u8]::is_ascii` call resolves against.
/// See [`std::slice`].
pub mod ascii {
    use super::Slice;
    use rust_primitives::slice::*;

    // The model of `u8` carries no `is_ascii_whitespace`/`to_ascii_*` yet, and
    // these are plain integer arithmetic.
    fn is_ascii_whitespace_byte(b: u8) -> bool {
        b == 32 || b == 9 || b == 10 || b == 12 || b == 13
    }
    fn to_ascii_lowercase_byte(b: u8) -> u8 {
        if b >= 65 && b <= 90 { b + 32 } else { b }
    }
    fn to_ascii_uppercase_byte(b: u8) -> u8 {
        if b >= 97 && b <= 122 { b - 32 } else { b }
    }

    impl Slice<u8> {
        /// See [`std::slice::is_ascii`]
        // opaque for F*: bounded loop over the slice.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn is_ascii(s: &[u8]) -> bool {
            let mut res = true;
            for i in 0..slice_length(s) {
                if *slice_index(s, i) > 127 {
                    res = false;
                }
            }
            res
        }
        /// See [`std::slice::eq_ignore_ascii_case`]
        // opaque for F*: see `is_ascii`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn eq_ignore_ascii_case(s: &[u8], other: &[u8]) -> bool {
            if slice_length(s) != slice_length(other) {
                false
            } else {
                let mut res = true;
                for i in 0..slice_length(s) {
                    if to_ascii_lowercase_byte(*slice_index(s, i))
                        != to_ascii_lowercase_byte(*slice_index(other, i))
                    {
                        res = false;
                    }
                }
                res
            }
        }
        /// See [`std::slice::trim_ascii_start`]
        // opaque for F*: see `is_ascii`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn trim_ascii_start(s: &[u8]) -> &[u8] {
            let len = slice_length(s);
            // `len` doubles as "no non-whitespace byte found", i.e. trim it all.
            let mut start = len;
            for i in 0..len {
                if start == len && !is_ascii_whitespace_byte(*slice_index(s, i)) {
                    start = i;
                }
            }
            slice_slice(s, start, len)
        }
        /// See [`std::slice::trim_ascii_end`]
        // opaque for F*: see `is_ascii`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn trim_ascii_end(s: &[u8]) -> &[u8] {
            let mut end = 0;
            for i in 0..slice_length(s) {
                if !is_ascii_whitespace_byte(*slice_index(s, i)) {
                    end = i + 1;
                }
            }
            slice_slice(s, 0, end)
        }
        /// See [`std::slice::trim_ascii`]
        pub(super) fn trim_ascii(s: &[u8]) -> &[u8] {
            Self::trim_ascii_end(Self::trim_ascii_start(s))
        }
        /// See [`std::slice::make_ascii_lowercase`]
        // F*-only: for-loop + indexed mutation, like `fill`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn make_ascii_lowercase(s: &mut [u8]) {
            for i in 0..slice_length(s) {
                let b = *slice_index(s, i);
                *slice_index_mut(s, i) = to_ascii_lowercase_byte(b);
            }
        }
        /// See [`std::slice::make_ascii_uppercase`]
        // F*-only: see `make_ascii_lowercase`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub(super) fn make_ascii_uppercase(s: &mut [u8]) {
            for i in 0..slice_length(s) {
                let b = *slice_index(s, i);
                *slice_index_mut(s, i) = to_ascii_uppercase_byte(b);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Slice;
    use crate::iter::traits::iterator::Iterator as ModelIterator;
    use crate::option::Option as ModelOption;
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// The slice iterators are lazy; draining them is what observes them.
    fn drain<I: ModelIterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let ModelOption::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

    proptest! {
        #[test]
        fn test_iter(slice in prop::collection::vec(any::<u8>(), 0..=20)) {
            prop_assert_eq!(
                drain(Slice::iter(&slice[..])),
                slice.iter().collect::<Vec<_>>()
            );
        }

        // Sizes run one past the slice length: `chunks` keeps a short final
        // chunk, `chunks_exact` drops it.
        #[test]
        fn test_chunks(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                drain(Slice::chunks(&slice[..], cs)),
                slice.chunks(cs).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_chunks_exact(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                drain(Slice::chunks_exact(&slice[..], cs)),
                slice.chunks_exact(cs).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_windows(slice in prop::collection::vec(any::<u8>(), 0..=20), size in 1usize..=21) {
            prop_assert_eq!(
                drain(Slice::windows(&slice[..], size)),
                slice.windows(size).collect::<Vec<_>>()
            );
        }

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
            let mut model_dest = vec![0u8; src.len()];
            let mut std_dest = model_dest.clone();
            Slice::copy_from_slice(&mut model_dest[..], &src[..]);
            std_dest.copy_from_slice(&src[..]);
            prop_assert_eq!(model_dest, std_dest);
        }

        #[test]
        fn test_clone_from_slice(src in prop::collection::vec(any::<u8>(), 1..=10)) {
            let mut model_dest = vec![0u8; src.len()];
            let mut std_dest = model_dest.clone();
            Slice::clone_from_slice(&mut model_dest[..], &src[..]);
            std_dest.clone_from_slice(&src[..]);
            prop_assert_eq!(model_dest, std_dest);
        }

        #[test]
        fn test_get_usize(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in prop_oneof![0usize..=11, any::<usize>()]) {
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

        // Two equal, non-empty slices: the element loop's accumulator is only
        // exercised in its stays-true form here, which independent draws
        // essentially never produce.
        #[test]
        fn test_slice_eq_reflexive(a in prop::collection::vec(any::<u8>(), 1..=8)) {
            prop_assert!(<[u8] as crate::cmp::PartialEq<[u8]>>::eq(&a[..], &a[..]));
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

        // A shared prefix guarantees at least one `Equal` element comparison,
        // which two independent slices only reach by chance.
        #[test]
        fn test_slice_cmp_shared_prefix(
            prefix in prop::collection::vec(any::<u8>(), 1..=4),
            a_tail in prop::collection::vec(any::<u8>(), 0..=4),
            b_tail in prop::collection::vec(any::<u8>(), 0..=4),
        ) {
            let mut a = prefix.clone();
            a.extend(a_tail);
            let mut b = prefix;
            b.extend(b_tail);
            prop_assert_eq!(
                <[u8] as crate::cmp::Ord>::cmp(&a[..], &b[..]),
                a[..].cmp(&b[..]).inject()
            );
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialOrd<[u8]>>::partial_cmp(&a[..], &b[..]),
                a[..].partial_cmp(&b[..]).inject()
            );
        }

        // `[T]: PartialEq<[U; N]>` — slice vs array (`s == [..]`). `use_equal`
        // biases toward the equal case, which random slices rarely hit.
        #[test]
        // `use_equal` makes the equal case common, which is what `ne` turns on.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_ne_slice(
            a in prop::collection::vec(0u8..4, 0..=4),
            b in prop::collection::vec(0u8..4, 0..=4),
            use_equal in any::<bool>(),
        ) {
            let b: Vec<u8> = if use_equal { a.clone() } else { b };
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialEq<[u8]>>::ne(&a[..], &b[..]),
                a[..] != b[..]
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_ne_slice_array(
            arr in any::<[u8; 3]>(),
            other in any::<[u8; 3]>(),
            kind in 0u8..3,
        ) {
            // All three shapes: equal, same length but different (the
            // element-wise loop), and a length mismatch (the early `false`).
            let v: Vec<u8> = match kind {
                0 => arr.to_vec(),
                1 => other.to_vec(),
                _ => vec![arr[0]],
            };
            let s: &[u8] = &v[..];
            prop_assert_eq!(
                <[u8] as crate::cmp::PartialEq<[u8; 3]>>::ne(s, &arr),
                s != arr
            );
        }

        // `index_mut` writes through the model's `IndexMut` (`v[i] = x`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_index_mut(v in prop::collection::vec(any::<u8>(), 1..=8), x in any::<u8>()) {
            let mut model = v.clone();
            let mut std_v = v.clone();
            let i = x as usize % v.len();
            *crate::ops::index::IndexMut::index_mut(&mut model[..], i) = x;
            std_v[i] = x;
            prop_assert_eq!(model, std_v);
        }

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

        // `get_mut` / `get_unchecked_mut` have no F* model.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_mut_usize(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in prop_oneof![0usize..=11, any::<usize>()], v in any::<u8>()) {
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

        #[cfg(not(hax_backend_fstar))]
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

        #[cfg(not(hax_backend_fstar))]
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

        #[cfg(not(hax_backend_fstar))]
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

        #[cfg(not(hax_backend_fstar))]
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

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_unchecked_mut_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            *Slice::get_unchecked_mut(&mut model[..], idx) = v;
            unsafe { *std_slice.get_unchecked_mut(idx) = v; }
            prop_assert_eq!(model, std_slice);
        }

        // ----- binary_search -------------------------------------------------

        // Sorted and deduplicated, so std's "any matching index" is the only one
        // and the two results can be compared exactly. `needle` is drawn from the
        // same domain, hitting both the `Ok` and the `Err` side.
        #[test]
        fn test_binary_search(
            values in prop::collection::vec(0u8..=30, 0..=12),
            needle in 0u8..=30,
        ) {
            let mut sorted = values;
            sorted.sort();
            sorted.dedup();
            prop_assert_eq!(
                Slice::binary_search(&sorted[..], &needle),
                sorted.binary_search(&needle).inject()
            );
        }

        // ----- SliceIndex::index and Index for [T] ---------------------------

        #[test]
        fn test_slice_index_trait_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4) {
            use crate::slice::index::SliceIndex;
            prop_assert_eq!(SliceIndex::index(idx, &slice[..]), &slice[idx]);
        }

        #[test]
        fn test_slice_index_trait_range(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..8, len in 0usize..8) {
            use crate::slice::index::SliceIndex;
            let end = (start + len).min(8);
            prop_assert_eq!(
                SliceIndex::index(crate::ops::range::Range { start, end }, &slice[..]),
                &slice[start..end]
            );
        }

        #[test]
        fn test_slice_index_trait_range_to(slice in prop::collection::vec(any::<u8>(), 8..=8), end in 0usize..=8) {
            use crate::slice::index::SliceIndex;
            prop_assert_eq!(
                SliceIndex::index(crate::ops::range::RangeTo { end }, &slice[..]),
                &slice[..end]
            );
        }

        #[test]
        fn test_slice_index_trait_range_from(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..=8) {
            use crate::slice::index::SliceIndex;
            prop_assert_eq!(
                SliceIndex::index(crate::ops::range::RangeFrom { start }, &slice[..]),
                &slice[start..]
            );
        }

        #[test]
        fn test_slice_index_trait_range_full(slice in prop::collection::vec(any::<u8>(), 0..=8)) {
            use crate::slice::index::SliceIndex;
            prop_assert_eq!(
                SliceIndex::index(crate::ops::range::RangeFull, &slice[..]),
                &slice[..]
            );
        }

        // `Index<I> for [T]`, as opposed to the `Index for &[T]` impls the
        // `test_index_*` tests above reach.
        #[test]
        fn test_unsized_index_usize(slice in prop::collection::vec(any::<u8>(), 4..=4), idx in 0usize..4) {
            prop_assert_eq!(
                <[u8] as crate::ops::index::Index<usize>>::index(&slice[..], idx),
                &slice[idx]
            );
        }

        // ----- in-bounds `get` / `get_mut` on `usize` ------------------------
        //
        // The `test_get_usize` / `test_get_mut_usize` tests above draw the index
        // from the whole `usize` range, so they only ever see `None`.

        #[test]
        fn test_get_usize_in_bounds(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in 0usize..10) {
            let idx = idx % slice.len();
            prop_assert_eq!(
                Slice::get(&slice[..], idx).map(|v: &u8| *v),
                slice.get(idx).copied().inject()
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_mut_usize_in_bounds(slice in prop::collection::vec(any::<u8>(), 1..=10), idx in 0usize..10, v in any::<u8>()) {
            let idx = idx % slice.len();
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

        // ----- IntoIterator for &[T] -----------------------------------------

        #[test]
        fn test_slice_into_iter(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let it = crate::iter::traits::collect::IntoIterator::into_iter(&slice[..]);
            prop_assert_eq!(drain(it), slice.iter().collect::<Vec<_>>());
        }

        // ----- get_unchecked_mut for the remaining range kinds ---------------

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_unchecked_mut_range_from(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..=8, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::get_unchecked_mut(&mut model[..], crate::ops::range::RangeFrom { start }).fill(v);
            unsafe { std_slice.get_unchecked_mut(start..).fill(v); }
            prop_assert_eq!(model, std_slice);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_unchecked_mut_range_to(slice in prop::collection::vec(any::<u8>(), 8..=8), end in 0usize..=8, v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::get_unchecked_mut(&mut model[..], crate::ops::range::RangeTo { end }).fill(v);
            unsafe { std_slice.get_unchecked_mut(..end).fill(v); }
            prop_assert_eq!(model, std_slice);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_unchecked_mut_range_full(slice in prop::collection::vec(any::<u8>(), 0..=8), v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::get_unchecked_mut(&mut model[..], crate::ops::range::RangeFull).fill(v);
            unsafe { std_slice.get_unchecked_mut(..).fill(v); }
            prop_assert_eq!(model, std_slice);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_get_unchecked_mut_range(slice in prop::collection::vec(any::<u8>(), 8..=8), start in 0usize..8, len in 0usize..8, v in any::<u8>()) {
            let end = (start + len).min(8);
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::get_unchecked_mut(&mut model[..], crate::ops::range::Range { start, end }).fill(v);
            unsafe { std_slice.get_unchecked_mut(start..end).fill(v); }
            prop_assert_eq!(model, std_slice);
        }

        // ----- rchunks / rchunks_exact / remainder ---------------------------

        // Sizes run one past the slice length, so the "shorter than one chunk"
        // and "nothing at all" branches are both exercised.
        #[test]
        fn test_rchunks(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                drain(Slice::rchunks(&slice[..], cs)),
                slice.rchunks(cs).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_rchunks_exact(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                drain(Slice::rchunks_exact(&slice[..], cs)),
                slice.rchunks_exact(cs).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_rchunks_exact_remainder(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                Slice::rchunks_exact(&slice[..], cs).remainder(),
                slice.rchunks_exact(cs).remainder()
            );
        }

        #[test]
        fn test_chunks_exact_remainder(slice in prop::collection::vec(any::<u8>(), 0..=20), cs in 1usize..=21) {
            prop_assert_eq!(
                Slice::chunks_exact(&slice[..], cs).remainder(),
                slice.chunks_exact(cs).remainder()
            );
        }

        // ----- split iterators ------------------------------------------------
        // The element range is kept small so the predicate actually fires.

        #[test]
        fn test_split(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                drain(Slice::split(&slice[..], p)),
                slice.split(p).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_split_as_slice(slice in prop::collection::vec(0u8..4, 0..=14), steps in 0usize..5) {
            let p = |x: &u8| *x == 0;
            let mut model = Slice::split(&slice[..], p);
            let mut std_split = slice.split(p);
            for _ in 0..steps {
                ModelIterator::next(&mut model);
                std_split.next();
            }
            prop_assert_eq!(model.as_slice(), std_split.as_slice());
        }

        #[test]
        fn test_split_inclusive(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                drain(Slice::split_inclusive(&slice[..], p)),
                slice.split_inclusive(p).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_splitn(slice in prop::collection::vec(0u8..4, 0..=14), n in 0usize..5) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                drain(Slice::splitn(&slice[..], n, p)),
                slice.splitn(n, p).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_rsplit(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                drain(Slice::rsplit(&slice[..], p)),
                slice.rsplit(p).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_rsplitn(slice in prop::collection::vec(0u8..4, 0..=14), n in 0usize..5) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                drain(Slice::rsplitn(&slice[..], n, p)),
                slice.rsplitn(n, p).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_chunk_by(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |a: &u8, b: &u8| a <= b;
            prop_assert_eq!(
                drain(Slice::chunk_by(&slice[..], p)),
                slice.chunk_by(p).collect::<Vec<_>>()
            );
        }

        // ----- split_once / rsplit_once --------------------------------------

        #[test]
        fn test_split_once(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                Slice::split_once(&slice[..], p),
                slice.split_once(p).inject()
            );
        }

        #[test]
        fn test_rsplit_once(slice in prop::collection::vec(0u8..4, 0..=14)) {
            let p = |x: &u8| *x == 0;
            prop_assert_eq!(
                Slice::rsplit_once(&slice[..], p),
                slice.rsplit_once(p).inject()
            );
        }

        // ----- split_first / split_last / as_slice ---------------------------

        #[test]
        fn test_split_first(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let model = match Slice::split_first(&slice[..]) {
                ModelOption::Some((v, rest)) => Some((*v, rest)),
                ModelOption::None => None,
            };
            prop_assert_eq!(model, slice.split_first().map(|(v, rest)| (*v, rest)));
        }

        #[test]
        fn test_split_last(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let model = match Slice::split_last(&slice[..]) {
                ModelOption::Some((v, rest)) => Some((*v, rest)),
                ModelOption::None => None,
            };
            prop_assert_eq!(model, slice.split_last().map(|(v, rest)| (*v, rest)));
        }

        // `<[T]>::as_slice` is unstable, so the expectation is pinned here: it is
        // the identity.
        #[test]
        fn test_as_slice(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(Slice::as_slice(&slice[..]), &slice[..]);
        }

        // ----- split_at_unchecked / swap_unchecked (in-bounds only) ----------

        #[test]
        fn test_split_at_unchecked(slice in prop::collection::vec(any::<u8>(), 0..=10), mid in 0usize..=10) {
            let mid = mid.min(slice.len());
            prop_assert_eq!(
                Slice::split_at_unchecked(&slice[..], mid),
                unsafe { slice.split_at_unchecked(mid) }
            );
        }

        #[test]
        fn test_swap_unchecked(slice in prop::collection::vec(any::<u8>(), 1..=10), a in 0usize..10, b in 0usize..10) {
            let a = a % slice.len();
            let b = b % slice.len();
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::swap_unchecked(&mut model[..], a, b);
            unsafe { std_slice.swap_unchecked(a, b) };
            prop_assert_eq!(model, std_slice);
        }

        // ----- rotate_left / rotate_right ------------------------------------

        #[test]
        fn test_rotate_left(slice in prop::collection::vec(any::<u8>(), 0..=10), mid in 0usize..=10) {
            let mid = mid.min(slice.len());
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::rotate_left(&mut model[..], mid);
            std_slice.rotate_left(mid);
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_rotate_right(slice in prop::collection::vec(any::<u8>(), 0..=10), k in 0usize..=10) {
            let k = k.min(slice.len());
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::rotate_right(&mut model[..], k);
            std_slice.rotate_right(k);
            prop_assert_eq!(model, std_slice);
        }

        // ----- fill_with ------------------------------------------------------

        #[test]
        fn test_fill_with(value in any::<u8>(), len in 0usize..=10) {
            let mut model = vec![0u8; len];
            let mut std_slice = vec![0u8; len];
            Slice::fill_with(&mut model[..], || value);
            std_slice.fill_with(|| value);
            prop_assert_eq!(model, std_slice);
        }

        // ----- binary_search_by / _by_key / partition_point -------------------
        // Unsorted inputs are included on purpose: the model replicates std's
        // probe sequence, so the two must agree there too.

        #[test]
        fn test_binary_search_by(slice in prop::collection::vec(any::<u8>(), 0..=12), x in any::<u8>()) {
            prop_assert_eq!(
                Slice::binary_search_by(&slice[..], |p: &u8| p.cmp(&x).inject()),
                slice.binary_search_by(|p| p.cmp(&x)).inject()
            );
        }

        #[test]
        fn test_binary_search_by_sorted(mut slice in prop::collection::vec(any::<u8>(), 0..=12), x in any::<u8>()) {
            slice.sort();
            prop_assert_eq!(
                Slice::binary_search_by(&slice[..], |p: &u8| p.cmp(&x).inject()),
                slice.binary_search_by(|p| p.cmp(&x)).inject()
            );
        }

        #[test]
        fn test_binary_search_by_key(mut slice in prop::collection::vec(any::<u8>(), 0..=12), x in any::<u8>()) {
            slice.sort();
            prop_assert_eq!(
                Slice::binary_search_by_key(&slice[..], &x, |p: &u8| *p),
                slice.binary_search_by_key(&x, |p| *p).inject()
            );
        }

        #[test]
        fn test_partition_point(mut slice in prop::collection::vec(any::<u8>(), 0..=12), x in any::<u8>()) {
            slice.sort();
            prop_assert_eq!(
                Slice::partition_point(&slice[..], |p: &u8| *p < x),
                slice.partition_point(|p| *p < x)
            );
        }

        #[test]
        fn test_partition_point_unsorted(slice in prop::collection::vec(any::<u8>(), 0..=12), x in any::<u8>()) {
            prop_assert_eq!(
                Slice::partition_point(&slice[..], |p: &u8| *p < x),
                slice.partition_point(|p| *p < x)
            );
        }

        // ----- is_sorted / is_sorted_by / is_sorted_by_key --------------------

        #[test]
        fn test_is_sorted(slice in prop::collection::vec(0u8..4, 0..=8)) {
            prop_assert_eq!(Slice::is_sorted(&slice[..]), slice.is_sorted());
        }

        #[test]
        fn test_is_sorted_sorted(mut slice in prop::collection::vec(0u8..4, 0..=8)) {
            slice.sort();
            prop_assert_eq!(Slice::is_sorted(&slice[..]), slice.is_sorted());
        }

        #[test]
        fn test_is_sorted_by(slice in prop::collection::vec(0u8..4, 0..=8)) {
            let p = |a: &u8, b: &u8| a < b;
            prop_assert_eq!(Slice::is_sorted_by(&slice[..], p), slice.is_sorted_by(p));
        }

        #[test]
        fn test_is_sorted_by_key(slice in prop::collection::vec(0u8..4, 0..=8)) {
            let f = |x: &u8| *x;
            prop_assert_eq!(Slice::is_sorted_by_key(&slice[..], f), slice.is_sorted_by_key(f));
        }

        // ----- first_mut / last_mut / as_mut_slice ---------------------------

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_first_mut(slice in prop::collection::vec(any::<u8>(), 0..=10), v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let ModelOption::Some(r) = Slice::first_mut(&mut model[..]) {
                *r = v;
            }
            if let Some(r) = std_slice.first_mut() {
                *r = v;
            }
            prop_assert_eq!(model, std_slice);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_last_mut(slice in prop::collection::vec(any::<u8>(), 0..=10), v in any::<u8>()) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            if let ModelOption::Some(r) = Slice::last_mut(&mut model[..]) {
                *r = v;
            }
            if let Some(r) = std_slice.last_mut() {
                *r = v;
            }
            prop_assert_eq!(model, std_slice);
        }

        // `<[T]>::as_mut_slice` is unstable, so the expectation is pinned: it is
        // the identity.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_as_mut_slice(slice in prop::collection::vec(any::<u8>(), 0..=10), v in any::<u8>()) {
            let mut model = slice.clone();
            let expected = vec![v; slice.len()];
            Slice::as_mut_slice(&mut model[..]).fill(v);
            prop_assert_eq!(model, expected);
        }

        // ----- split_off_first / split_off_last ------------------------------

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_split_off_first(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let mut model: &[u8] = &slice[..];
            let mut std_slice: &[u8] = &slice[..];
            let m = Slice::split_off_first(&mut model).map(|v: &u8| *v);
            let s = std_slice.split_off_first().copied();
            prop_assert_eq!(m, s.inject());
            prop_assert_eq!(model, std_slice);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_split_off_last(slice in prop::collection::vec(any::<u8>(), 0..=10)) {
            let mut model: &[u8] = &slice[..];
            let mut std_slice: &[u8] = &slice[..];
            let m = Slice::split_off_last(&mut model).map(|v: &u8| *v);
            let s = std_slice.split_off_last().copied();
            prop_assert_eq!(m, s.inject());
            prop_assert_eq!(model, std_slice);
        }

        // ----- SlicePattern + strip_* / trim_* -------------------------------

        #[test]
        fn test_slice_pattern_as_slice(slice in prop::collection::vec(any::<u8>(), 0..=10), arr in any::<[u8; 3]>()) {
            prop_assert_eq!(
                crate::slice::SlicePattern::as_slice(&slice[..]),
                core::slice::SlicePattern::as_slice(&slice[..])
            );
            prop_assert_eq!(
                crate::slice::SlicePattern::as_slice(&arr),
                core::slice::SlicePattern::as_slice(&arr)
            );
        }

        // `use_prefix` biases toward the matching case, which random slices
        // essentially never hit.
        #[test]
        fn test_strip_prefix(slice in prop::collection::vec(0u8..4, 0..=10), other in prop::collection::vec(0u8..4, 0..=4), n in 0usize..=4, use_prefix in any::<bool>()) {
            let n = n.min(slice.len());
            let prefix: Vec<u8> = if use_prefix { slice[..n].to_vec() } else { other };
            prop_assert_eq!(
                Slice::strip_prefix(&slice[..], &prefix[..]),
                slice.strip_prefix(&prefix[..]).inject()
            );
        }

        #[test]
        fn test_strip_suffix(slice in prop::collection::vec(0u8..4, 0..=10), other in prop::collection::vec(0u8..4, 0..=4), n in 0usize..=4, use_suffix in any::<bool>()) {
            let n = n.min(slice.len());
            let suffix: Vec<u8> = if use_suffix { slice[slice.len() - n..].to_vec() } else { other };
            prop_assert_eq!(
                Slice::strip_suffix(&slice[..], &suffix[..]),
                slice.strip_suffix(&suffix[..]).inject()
            );
        }

        // The array `SlicePattern` impl, which the slice one does not exercise.
        #[test]
        fn test_strip_prefix_array(slice in prop::collection::vec(0u8..4, 0..=10), prefix in any::<[u8; 2]>()) {
            prop_assert_eq!(
                Slice::strip_prefix(&slice[..], &prefix),
                slice.strip_prefix(&prefix).inject()
            );
        }

        #[test]
        fn test_trim_prefix(slice in prop::collection::vec(0u8..4, 0..=10), other in prop::collection::vec(0u8..4, 0..=4), n in 0usize..=4, use_prefix in any::<bool>()) {
            let n = n.min(slice.len());
            let prefix: Vec<u8> = if use_prefix { slice[..n].to_vec() } else { other };
            prop_assert_eq!(
                Slice::trim_prefix(&slice[..], &prefix[..]),
                slice.trim_prefix(&prefix[..])
            );
        }

        #[test]
        fn test_trim_suffix(slice in prop::collection::vec(0u8..4, 0..=10), other in prop::collection::vec(0u8..4, 0..=4), n in 0usize..=4, use_suffix in any::<bool>()) {
            let n = n.min(slice.len());
            let suffix: Vec<u8> = if use_suffix { slice[slice.len() - n..].to_vec() } else { other };
            prop_assert_eq!(
                Slice::trim_suffix(&slice[..], &suffix[..]),
                slice.trim_suffix(&suffix[..])
            );
        }

        #[test]
        fn test_strip_circumfix(slice in prop::collection::vec(0u8..4, 0..=10), n in 0usize..=3, m in 0usize..=3, matching in any::<bool>()) {
            let n = n.min(slice.len());
            let m = m.min(slice.len() - n);
            let (prefix, suffix): (Vec<u8>, Vec<u8>) = if matching {
                (slice[..n].to_vec(), slice[slice.len() - m..].to_vec())
            } else {
                (vec![1, 1, 1], vec![2, 2, 2])
            };
            prop_assert_eq!(
                Slice::strip_circumfix(&slice[..], &prefix[..], &suffix[..]),
                slice.strip_circumfix(&prefix[..], &suffix[..]).inject()
            );
        }

        // ----- [u8] ASCII helpers --------------------------------------------
        // `0..=130` straddles the ASCII boundary; `9..=32` is mostly whitespace.

        #[test]
        fn test_is_ascii(slice in prop::collection::vec(0u8..=130, 0..=12)) {
            prop_assert_eq!(Slice::is_ascii(&slice[..]), slice.is_ascii());
        }

        #[test]
        fn test_eq_ignore_ascii_case(a in prop::collection::vec(60u8..=130, 0..=8), b in prop::collection::vec(60u8..=130, 0..=8)) {
            prop_assert_eq!(
                Slice::eq_ignore_ascii_case(&a[..], &b[..]),
                a.eq_ignore_ascii_case(&b[..])
            );
        }

        // Equal-length pairs make the per-byte comparison, not the length check,
        // the deciding factor.
        #[test]
        fn test_eq_ignore_ascii_case_same_len(pairs in prop::collection::vec((60u8..=130, 60u8..=130), 0..=8)) {
            let a: Vec<u8> = pairs.iter().map(|p| p.0).collect();
            let b: Vec<u8> = pairs.iter().map(|p| p.1).collect();
            prop_assert_eq!(
                Slice::eq_ignore_ascii_case(&a[..], &b[..]),
                a.eq_ignore_ascii_case(&b[..])
            );
        }

        #[test]
        fn test_trim_ascii_start(slice in prop::collection::vec(9u8..=32, 0..=12)) {
            prop_assert_eq!(Slice::trim_ascii_start(&slice[..]), slice.trim_ascii_start());
        }

        #[test]
        fn test_trim_ascii_end(slice in prop::collection::vec(9u8..=32, 0..=12)) {
            prop_assert_eq!(Slice::trim_ascii_end(&slice[..]), slice.trim_ascii_end());
        }

        #[test]
        fn test_trim_ascii(slice in prop::collection::vec(9u8..=32, 0..=12)) {
            prop_assert_eq!(Slice::trim_ascii(&slice[..]), slice.trim_ascii());
        }

        #[test]
        fn test_make_ascii_lowercase(slice in prop::collection::vec(0u8..=130, 0..=12)) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::make_ascii_lowercase(&mut model[..]);
            std_slice.make_ascii_lowercase();
            prop_assert_eq!(model, std_slice);
        }

        #[test]
        fn test_make_ascii_uppercase(slice in prop::collection::vec(0u8..=130, 0..=12)) {
            let mut model = slice.clone();
            let mut std_slice = slice.clone();
            Slice::make_ascii_uppercase(&mut model[..]);
            std_slice.make_ascii_uppercase();
            prop_assert_eq!(model, std_slice);
        }
    }

    #[test]
    fn test_rchunks_zero_panics() {
        crate::testing::panics_like_core(
            || Slice::rchunks(&[1u8, 2, 3][..], 0),
            || [1u8, 2, 3].rchunks(0),
        );
    }

    #[test]
    fn test_rchunks_exact_zero_panics() {
        crate::testing::panics_like_core(
            || Slice::rchunks_exact(&[1u8, 2, 3][..], 0),
            || [1u8, 2, 3].rchunks_exact(0),
        );
    }

    #[test]
    fn test_rotate_left_past_end_panics() {
        crate::testing::panics_like_core(
            || Slice::rotate_left(&mut [1u8, 2, 3][..], 4),
            || [1u8, 2, 3].rotate_left(4),
        );
    }

    #[test]
    fn test_rotate_right_past_end_panics() {
        crate::testing::panics_like_core(
            || Slice::rotate_right(&mut [1u8, 2, 3][..], 4),
            || [1u8, 2, 3].rotate_right(4),
        );
    }

    #[test]
    fn test_chunks_zero_panics() {
        crate::testing::panics_like_core(
            || Slice::chunks(&[1u8, 2, 3][..], 0),
            || [1u8, 2, 3].chunks(0),
        );
    }

    #[test]
    fn test_chunks_exact_zero_panics() {
        crate::testing::panics_like_core(
            || Slice::chunks_exact(&[1u8, 2, 3][..], 0),
            || [1u8, 2, 3].chunks_exact(0),
        );
    }

    #[test]
    fn test_windows_zero_panics() {
        crate::testing::panics_like_core(
            || Slice::windows(&[1u8, 2, 3][..], 0),
            || [1u8, 2, 3].windows(0),
        );
    }

    #[test]
    fn test_split_at_past_end_panics() {
        crate::testing::panics_like_core(
            || Slice::split_at(&[1u8, 2, 3][..], 4),
            || [1u8, 2, 3].split_at(4),
        );
    }

    #[test]
    fn test_swap_out_of_bounds_panics() {
        crate::testing::panics_like_core(
            || Slice::swap(&mut [1u8, 2, 3][..], 0, 3),
            || [1u8, 2, 3].swap(0, 3),
        );
    }

    #[test]
    fn test_copy_from_slice_length_mismatch_panics() {
        crate::testing::panics_like_core(
            || Slice::copy_from_slice(&mut [0u8; 3][..], &[1u8, 2][..]),
            || [0u8; 3].copy_from_slice(&[1u8, 2][..]),
        );
    }

    #[test]
    fn test_clone_from_slice_length_mismatch_panics() {
        crate::testing::panics_like_core(
            || Slice::clone_from_slice(&mut [0u8; 3][..], &[1u8, 2][..]),
            || [0u8; 3].clone_from_slice(&[1u8, 2][..]),
        );
    }

    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_index_out_of_bounds_panics() {
        // `black_box` the index: a literal one is a compile-time error, not a panic.
        let (model, real): (&[u8], [u8; 3]) = (&[1u8, 2, 3], [1u8, 2, 3]);
        let i = std::hint::black_box(3usize);
        crate::testing::panics_like_core(|| model[i], || real[i]);
    }

    // `Index<I> for [T]` panics through its `Option::None` arm.
    #[test]
    fn test_unsized_index_out_of_bounds_panics() {
        let (model, real): (&[u8], [u8; 3]) = (&[1u8, 2, 3], [1u8, 2, 3]);
        let i = std::hint::black_box(3usize);
        crate::testing::panics_like_core(
            || <[u8] as crate::ops::index::Index<usize>>::index(model, i),
            || real[i],
        );
    }

    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_index_range_past_end_panics() {
        let (model, real): (&[u8], [u8; 3]) = (&[1u8, 2, 3], [1u8, 2, 3]);
        let end = std::hint::black_box(4usize);
        crate::testing::panics_like_core(|| &model[1..end], || &real[1..end]);
    }
}
