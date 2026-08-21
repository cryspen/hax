#![allow(unused)]
// `coverage(off)` is unstable; `cfg(coverage_nightly)` is set only by
// `cargo llvm-cov`, so normal builds and extraction never see this.
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]
// `Cow::is_borrowed` / `Cow::is_owned` are still unstable in the real `alloc`,
// and the property tests compare the model against them.
#![cfg_attr(test, feature(cow_is_borrowed))]
// The `Box` items modelled in `boxed` are still unstable in real `alloc`;
// the feature gates let the test module compare against them. They are
// `test`-only so the extracted crate stays on stable surface syntax.
#![cfg_attr(
    test,
    feature(
        allocator_api,
        box_into_boxed_slice,
        box_into_inner,
        push_mut,
        smart_pointer_try_map,
        try_with_capacity,
        vec_try_remove
    )
)]

#[cfg(test)]
mod testing {
    pub trait Inject {
        type Model;
        fn inject(&self) -> Self::Model;
    }

    /// Asserts the model and real `alloc` both panic on the same input.
    #[track_caller]
    pub fn panics_like_core<A, B>(model: impl FnOnce() -> A, core: impl FnOnce() -> B) {
        use std::panic::{AssertUnwindSafe, catch_unwind};
        let m = catch_unwind(AssertUnwindSafe(model));
        let c = catch_unwind(AssertUnwindSafe(core));
        assert!(m.is_err(), "the model did not panic");
        assert!(
            c.is_err(),
            "real `alloc` did not panic, so the model must not either"
        );
    }
}

mod alloc {
    pub trait Allocator {}

    #[cfg_attr(test, derive(PartialEq, Debug))]
    #[derive(Clone)]
    pub struct Global;

    impl Allocator for Global {}
}

mod borrow {
    // `ToOwned` comes first so that its blanket impl stays the module's first
    // impl block: F* names instances by position, and moving it would rename
    // `Alloc.Borrow.impl` out from under downstream proofs.
    /// See [`std::borrow::ToOwned`]
    // `requires(true)`, as on `core::cmp::PartialEq::eq`: without it F* gives
    // `to_owned` an abstract precondition that a caller holding only a
    // `t_ToOwned` dictionary (`Cow::into_owned`) cannot discharge.
    #[hax_lib::attributes]
    pub trait ToOwned {
        /// See [`std::borrow::ToOwned::Owned`]
        type Owned;
        /// See [`std::borrow::ToOwned::to_owned`]
        #[hax_lib::requires(true)]
        fn to_owned(self) -> Self::Owned;
    }
    // Mirrors real `alloc`'s `impl<T: Clone> ToOwned for T`. The `Clone` bound
    // matters for more than fidelity: a client's call site passes the `Clone`
    // dictionary, so a blanket impl without it is an arity mismatch.
    impl<T: Clone> ToOwned for T {
        type Owned = T;
        fn to_owned(self) -> T {
            self.clone()
        }
    }

    /// See [`std::borrow::Cow`]: std's two variants, with the `&'a B` of
    /// `Borrowed` erased to a plain `B` as hax erases shared borrows.
    // `noeq`: the `Owned` payload is the typeclass projection `i0.f_Owned`, which
    // F* cannot show supports decidable equality, so it must not try to derive it
    // for `t_Cow`. Same fix as `core::iter::Flatten`.
    #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
    pub enum Cow<B: ToOwned> {
        Borrowed(B),
        Owned(B::Owned),
    }

    impl<B: ToOwned> Cow<B> {
        /// See [`std::borrow::Cow::is_borrowed`]. Like std's, an associated
        /// function rather than a method, so it cannot clash with a method of
        /// the inner type.
        pub fn is_borrowed(c: &Cow<B>) -> bool {
            match c {
                Cow::Borrowed(_) => true,
                Cow::Owned(_) => false,
            }
        }
        /// See [`std::borrow::Cow::is_owned`]
        pub fn is_owned(c: &Cow<B>) -> bool {
            match c {
                Cow::Borrowed(_) => false,
                Cow::Owned(_) => true,
            }
        }
        /// See [`std::borrow::Cow::into_owned`]
        pub fn into_owned(self) -> B::Owned {
            match self {
                Cow::Borrowed(b) => b.to_owned(),
                Cow::Owned(o) => o,
            }
        }
        /// See [`std::borrow::Cow::to_mut`].
        //
        // DEVIATION(std): std promotes a `Borrowed` in place and hands out a
        // `&mut B::Owned` into `self`. The model cannot return a borrow into
        // `self`, so — as `Option::take` does for `&mut` signatures — it
        // consumes the `Cow` and returns the owned value the caller would have
        // mutated through. That makes it coincide with `into_owned`.
        pub fn to_mut(self) -> B::Owned {
            self.into_owned()
        }
    }

    /// `clone_into` is a trait *default* method in real `alloc`, which hax does
    /// not support. Like `core::cmp`'s `Neq` / `PartialOrdDefaults`, the model
    /// provides it through a blanket-implemented companion trait.
    // No `requires(true)` here, unlike on `ToOwned::to_owned`: for a parameter
    // typed by a *supertrait* projection, hax renders the precondition's type as
    // `i0.f_Owned`, a name that does not exist inside the generated F* class.
    // Nothing in the model calls `clone_into` through the abstract trait, so the
    // default (opaque) precondition costs nothing.
    pub trait ToOwnedDefaults: ToOwned {
        /// See [`std::borrow::ToOwned::clone_into`]
        fn clone_into(self, target: &mut Self::Owned);
    }
    impl<T: ToOwned> ToOwnedDefaults for T {
        fn clone_into(self, target: &mut T::Owned) {
            *target = self.to_owned()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{Cow, ToOwned, ToOwnedDefaults};
        use proptest::prelude::*;

        /// The model's blanket `ToOwned` has `Owned = Self`, which for `u8`
        /// agrees with real `alloc` (`<u8 as ToOwned>::Owned == u8`).
        proptest! {
            #[test]
            fn test_to_owned(x in any::<u8>()) {
                prop_assert_eq!(ToOwned::to_owned(x), std::borrow::ToOwned::to_owned(&x));
            }

            #[test]
            fn test_clone_into(x in any::<u8>(), y in any::<u8>()) {
                let mut model_target = y;
                ToOwnedDefaults::clone_into(x, &mut model_target);
                let mut std_target = y;
                std::borrow::ToOwned::clone_into(&x, &mut std_target);
                prop_assert_eq!(model_target, std_target);
            }

            #[test]
            fn test_is_borrowed_is_owned(x in any::<u8>()) {
                let model_b: Cow<u8> = Cow::Borrowed(x);
                let std_b: std::borrow::Cow<u8> = std::borrow::Cow::Borrowed(&x);
                prop_assert_eq!(Cow::is_borrowed(&model_b), std::borrow::Cow::is_borrowed(&std_b));
                prop_assert_eq!(Cow::is_owned(&model_b), std::borrow::Cow::is_owned(&std_b));

                let model_o: Cow<u8> = Cow::Owned(x);
                let std_o: std::borrow::Cow<u8> = std::borrow::Cow::Owned(x);
                prop_assert_eq!(Cow::is_borrowed(&model_o), std::borrow::Cow::is_borrowed(&std_o));
                prop_assert_eq!(Cow::is_owned(&model_o), std::borrow::Cow::is_owned(&std_o));
            }

            #[test]
            fn test_into_owned(x in any::<u8>()) {
                let std_b: std::borrow::Cow<u8> = std::borrow::Cow::Borrowed(&x);
                prop_assert_eq!(Cow::Borrowed(x).into_owned(), std_b.into_owned());
                let std_o: std::borrow::Cow<u8> = std::borrow::Cow::Owned(x);
                prop_assert_eq!(Cow::<u8>::Owned(x).into_owned(), std_o.into_owned());
            }

            /// The model's `to_mut` returns the owned value instead of a
            /// borrow into `self` (see its `DEVIATION` note), so it is compared
            /// against what std's `&mut` points at.
            #[test]
            fn test_to_mut(x in any::<u8>()) {
                let mut std_b: std::borrow::Cow<u8> = std::borrow::Cow::Borrowed(&x);
                prop_assert_eq!(Cow::Borrowed(x).to_mut(), *std_b.to_mut());
                let mut std_o: std::borrow::Cow<u8> = std::borrow::Cow::Owned(x);
                prop_assert_eq!(Cow::<u8>::Owned(x).to_mut(), *std_o.to_mut());
            }

            #[test]
            fn test_to_owned_vec(v in prop::collection::vec(any::<u8>(), 0..20)) {
                prop_assert_eq!(ToOwned::to_owned(v.clone()), v);
            }
        }
    }
}

mod boxed {
    pub struct Box<T>(pub T);
    impl<T> Box<T> {
        // Hax removes boxes, so this should be the identity
        fn new(v: T) -> T {
            v
        }
        /// See [`std::boxed::Box::new_in`]. The model has a single heap, so the
        /// allocator argument is ignored. The `A: Allocator` bound is omitted
        /// on purpose: extraction erases `Box`'s allocator clause at call
        /// sites, so a model that kept the bound would expect a dictionary
        /// nobody passes.
        fn new_in<A>(x: T, _alloc: A) -> T {
            x
        }
        /// See [`std::boxed::Box::into_inner`]. With boxes erased this is the
        /// identity, exactly like `new` in the other direction.
        fn into_inner(boxed: T) -> T {
            boxed
        }
        /// See [`std::boxed::Box::map`]. Real `map` reuses the allocation when
        /// the layouts match; with boxes erased only the value transformation
        /// is observable.
        fn map<U, F: FnOnce(T) -> U>(this: T, f: F) -> U {
            f(this)
        }
        /// See [`std::boxed::Box::into_boxed_slice`]: the one-element slice
        /// holding `boxed`.
        // `Box` names the model's own wrapper inside this module, so the real
        // boxed slice has to be spelled out (extraction erases it to `[T]`).
        fn into_boxed_slice(boxed: T) -> std::boxed::Box<[T]> {
            std::boxed::Box::new([boxed])
        }
    }

    #[cfg(test)]
    mod tests {
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_new_in(x in any::<u8>()) {
                prop_assert_eq!(
                    super::Box::<u8>::new_in(x, crate::alloc::Global),
                    *std::boxed::Box::new_in(x, std::alloc::Global)
                );
            }

            #[test]
            fn test_into_inner(x in any::<u8>()) {
                prop_assert_eq!(
                    super::Box::<u8>::into_inner(x),
                    std::boxed::Box::into_inner(std::boxed::Box::new(x))
                );
            }

            // The closure changes the type, so a `map` that ignored `f` and
            // returned its argument would not type-check, let alone pass.
            #[test]
            fn test_map(x in any::<u8>()) {
                let f = |v: u8| v as u32 * 3 + 1;
                prop_assert_eq!(
                    super::Box::<u8>::map(x, f),
                    *std::boxed::Box::map(std::boxed::Box::new(x), f)
                );
            }

            #[test]
            fn test_into_boxed_slice(x in any::<u8>()) {
                prop_assert_eq!(
                    super::Box::<u8>::into_boxed_slice(x),
                    std::boxed::Box::into_boxed_slice(std::boxed::Box::new(x))
                );
            }

            #[test]
            fn test_new_is_identity(x in any::<u8>()) {
                prop_assert_eq!(super::Box::<u8>::new(x), x);
            }
        }
    }
}

mod collections {
    // All implementations are dummy (for interfaces only)

    /// See [`std::collections::TryReserveErrorKind`].
    ///
    /// DEVIATION(std): std's `AllocError` variant carries the
    /// `core::alloc::Layout` of the failed request (plus a `#[doc(hidden)]`
    /// unit field). We do not model `Layout`, and the model's collections
    /// never fail to allocate, so the payload would be unobservable.
    #[cfg_attr(test, derive(PartialEq, Debug))]
    #[derive(Clone)]
    pub enum TryReserveErrorKind {
        CapacityOverflow,
        AllocError,
    }

    /// See [`std::collections::TryReserveError`]: the error returned by the
    /// `try_reserve` family. The model never fails to allocate, so no model
    /// operation ever produces one.
    #[cfg_attr(test, derive(PartialEq, Debug))]
    #[derive(Clone)]
    pub struct TryReserveError(TryReserveErrorKind);

    impl TryReserveError {
        /// See [`std::collections::TryReserveError::kind`] (unstable in std:
        /// `try_reserve_kind`), which returns a clone of the stored kind.
        fn kind(&self) -> TryReserveErrorKind {
            self.0.clone()
        }
    }

    /// Model of `alloc::collections::binary_heap`.
    ///
    /// DEVIATION(std): backed by an *unordered* `Vec`, not a sift-up/sift-down
    /// heap. `pop`/`peek` therefore scan for the maximum, which is why they
    /// carry a `T: Ord` bound even where std does not need one (std reads
    /// element 0 and relies on the heap invariant). Every documented
    /// observation is still reproduced: `as_slice`/`into_vec`/`iter` are
    /// explicitly "arbitrary order" in std, and `into_sorted_vec` sorts.
    ///
    /// This module is in `ALLOC_CHARON_EXCLUDES` (charon crashes on it), so it
    /// has an F* extraction but **no** Lean one.
    mod binary_heap {
        #[hax_lib::fstar::before("open Rust_primitives.Notations")]
        use crate::vec::*;
        #[cfg_attr(test, derive(PartialEq, Debug))]
        struct BinaryHeap<T, A>(Vec<T>, std::marker::PhantomData<A>);

        /// See [`std::collections::binary_heap::Iter`]
        pub struct Iter<'a, T>(pub rust_primitives::sequence::Seq<&'a T>);

        impl<'a, T> Iterator for Iter<'a, T> {
            type Item = &'a T;
            fn next(&mut self) -> Option<Self::Item> {
                if rust_primitives::sequence::seq_len(&self.0) == 0 {
                    None
                } else {
                    Some(rust_primitives::sequence::seq_remove(&mut self.0, 0))
                }
            }
        }

        // Padding impls; see the comment on `vec_deque`'s. Eight, because the
        // `Iterator for Iter` impl above is plain too and the three blocks
        // below carry `#[hax_lib::attributes]`, which puts them last — landing
        // them at 9, 10 and 11, which is where hax resolves real `alloc`'s
        // `BinaryHeap::{new, push, peek}` to.
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}

        #[hax_lib::attributes]
        impl<T> BinaryHeap<T, crate::alloc::Global> {
            /// See [`std::collections::BinaryHeap::new`]
            fn new() -> BinaryHeap<T, crate::alloc::Global> {
                BinaryHeap(
                    crate::vec::from_seq(rust_primitives::sequence::seq_empty()),
                    std::marker::PhantomData,
                )
            }
            /// See [`std::collections::BinaryHeap::with_capacity`]: capacity is
            /// not modeled, so this is `new`.
            fn with_capacity(_capacity: usize) -> BinaryHeap<T, crate::alloc::Global> {
                BinaryHeap::new()
            }
        }

        #[hax_lib::attributes]
        impl<T, A: crate::alloc::Allocator> BinaryHeap<T, A> {
            /// See [`std::collections::BinaryHeap::new_in`]
            fn new_in(_alloc: A) -> BinaryHeap<T, A> {
                BinaryHeap(
                    crate::vec::from_seq(rust_primitives::sequence::seq_empty()),
                    std::marker::PhantomData::<A>,
                )
            }
            /// See [`std::collections::BinaryHeap::with_capacity_in`]
            fn with_capacity_in(_capacity: usize, alloc: A) -> BinaryHeap<T, A> {
                BinaryHeap::new_in(alloc)
            }
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push(&mut self, v: T)
            where
                T: Ord,
            {
                self.0.push(v)
            }
            #[hax_lib::ensures(|res| (self.len() > 0) == res.is_some())]
            fn pop(&mut self) -> Option<T>
            where
                T: Ord,
            {
                let mut max: Option<&T> = None;
                let mut index = 0;
                for i in 0..self.len() {
                    // Not in the Lean lane: aeneas translates the invariant into `hax_lib`
                    // items the Lean library does not define.
                    #[cfg(not(charon))]
                    hax_lib::loop_invariant!(|i: usize| (i > 0) == max.is_some());
                    if max.is_none_or(|max| self.0[i] > *max) {
                        max = Some(&self.0[i]);
                        index = i;
                    }
                }
                if max.is_some() {
                    Some(self.0.remove(index))
                } else {
                    None
                }
            }
            /// See [`std::collections::BinaryHeap::append`]
            #[hax_lib::requires(hax_lib::ToInt::to_int(self.len()) + hax_lib::ToInt::to_int(other.len()) <= hax_lib::ToInt::to_int(core::primitive::usize::MAX))]
            fn append(&mut self, other: &mut BinaryHeap<T, A>)
            where
                T: Ord,
            {
                self.0.append(&mut other.0)
            }
            /// See [`std::collections::BinaryHeap::retain`].
            ///
            /// The loop walks from the back so a removal never shifts an
            /// index still to be visited. `FnMut` is std's bound, and the body
            /// is opaque for F* in exchange — see the note on
            /// `VecDeque::retain`.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn retain<F>(&mut self, mut f: F)
            where
                T: Ord,
                F: FnMut(&T) -> bool,
            {
                let l = self.len();
                for k in 0..l {
                    let i = l - 1 - k;
                    if i < self.len() && !f(&self.0[i]) {
                        let _removed = self.0.remove(i);
                    }
                }
            }
            /// See [`std::collections::BinaryHeap::into_sorted_vec`]: ascending.
            ///
            /// Opaque: the Rust body below is the specification (repeatedly move
            /// out the smallest remaining element), but proving the `Vec::push`
            /// bound through the loop needs an invariant relating two locals,
            /// which `hax_lib::loop_invariant!` cannot state here.
            #[hax_lib::opaque]
            fn into_sorted_vec(mut self) -> Vec<T>
            where
                T: Ord,
            {
                let mut out = crate::vec::Vec::new();
                let n = self.len();
                for _k in 0..n {
                    let mut min: Option<&T> = None;
                    let mut index = 0;
                    for i in 0..self.len() {
                        if min.is_none_or(|min| self.0[i] < *min) {
                            min = Some(&self.0[i]);
                            index = i;
                        }
                    }
                    if min.is_some() {
                        out.push(self.0.remove(index))
                    }
                }
                out
            }
        }

        #[hax_lib::attributes]
        impl<T, A: crate::alloc::Allocator> BinaryHeap<T, A> {
            fn len(&self) -> usize {
                self.0.len()
            }
            /// See [`std::collections::BinaryHeap::is_empty`]
            fn is_empty(&self) -> bool {
                self.0.len() == 0
            }
            /// See [`std::collections::BinaryHeap::clear`]
            fn clear(&mut self) {
                self.0 = crate::vec::from_seq(rust_primitives::sequence::seq_empty())
            }
            /// See [`std::collections::BinaryHeap::as_slice`]: arbitrary order,
            /// which for this model is insertion order.
            fn as_slice(&self) -> &[T] {
                self.0.as_slice()
            }
            /// See [`std::collections::BinaryHeap::into_vec`]: arbitrary order.
            fn into_vec(self) -> Vec<T> {
                self.0
            }
            /// See [`std::collections::BinaryHeap::iter`]: arbitrary order.
            fn iter(&self) -> Iter<'_, T> {
                Iter(rust_primitives::sequence::seq_from_slice(self.0.as_slice()))
            }
            /// See [`std::collections::BinaryHeap::reserve`]: capacity is not
            /// modeled, so this leaves the contents untouched.
            fn reserve(&mut self, _additional: usize) {}
            /// See [`std::collections::BinaryHeap::reserve_exact`]
            fn reserve_exact(&mut self, _additional: usize) {}
            /// See [`std::collections::BinaryHeap::shrink_to_fit`]
            fn shrink_to_fit(&mut self) {}
            /// See [`std::collections::BinaryHeap::shrink_to`]
            fn shrink_to(&mut self, _min_capacity: usize) {}
            /// See [`std::collections::BinaryHeap::try_reserve`]: the model never
            /// fails to allocate.
            fn try_reserve(&mut self, _additional: usize) -> Result<(), super::TryReserveError> {
                Ok(())
            }
            /// See [`std::collections::BinaryHeap::try_reserve_exact`]
            fn try_reserve_exact(
                &mut self,
                _additional: usize,
            ) -> Result<(), super::TryReserveError> {
                Ok(())
            }
            #[hax_lib::ensures(|res| (self.len() > 0) == res.is_some())]
            fn peek(&self) -> Option<&T>
            where
                T: Ord,
            {
                let mut max: Option<&T> = None;
                for i in 0..self.len() {
                    // Not in the Lean lane: aeneas translates the invariant into `hax_lib`
                    // items the Lean library does not define.
                    #[cfg(not(charon))]
                    hax_lib::loop_invariant!(|i: usize| (i > 0) == max.is_some());
                    if max.is_none_or(|max| self.0[i] > *max) {
                        max = Some(&self.0[i]);
                    }
                }
                max
            }
        }

        #[hax_lib::fstar::after(
            "
assume val lemma_peek_pop: #t:Type -> (#a: Type) -> (#i: Core_models.Cmp.t_Ord t) 
  -> (#i1: Alloc.Alloc.t_Allocator a) -> h: t_BinaryHeap t a
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek #t #a h)]
        "
        )]
        use core::*;

        #[cfg(test)]
        mod tests {
            use proptest::prelude::*;

            type Model<T> = super::BinaryHeap<T, crate::alloc::Global>;
            type Std<T> = std::collections::BinaryHeap<T>;

            fn build(elements: &[u8]) -> (Model<u8>, Std<u8>) {
                let mut model = Model::new();
                let mut std_heap = Std::new();
                for &e in elements {
                    model.push(e);
                    std_heap.push(e);
                }
                (model, std_heap)
            }

            /// `as_slice`/`into_vec`/`iter` are documented as "arbitrary order",
            /// so the only shared observation is the multiset of elements.
            fn sorted(mut v: std::vec::Vec<u8>) -> std::vec::Vec<u8> {
                v.sort();
                v
            }

            /// Pop everything: descending order, so this *is* comparable.
            fn drain_model(mut h: Model<u8>) -> std::vec::Vec<u8> {
                let mut out = std::vec::Vec::new();
                while let Some(x) = h.pop() {
                    out.push(x)
                }
                out
            }

            fn drain_std(mut h: Std<u8>) -> std::vec::Vec<u8> {
                let mut out = std::vec::Vec::new();
                while let Some(x) = h.pop() {
                    out.push(x)
                }
                out
            }

            proptest! {
                #[test]
                fn test_len_is_empty(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_heap) = build(&elements);
                    prop_assert_eq!(model.len(), std_heap.len());
                    prop_assert_eq!(model.is_empty(), std_heap.is_empty());
                }

                #[test]
                fn test_clear(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model, mut std_heap) = build(&elements);
                    model.clear();
                    std_heap.clear();
                    prop_assert_eq!(model.len(), std_heap.len());
                    prop_assert!(model.is_empty());
                }

                #[test]
                fn test_as_slice_and_iter(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_heap) = build(&elements);
                    prop_assert_eq!(sorted(model.as_slice().to_vec()),
                                    sorted(std_heap.as_slice().to_vec()));
                    let from_iter: std::vec::Vec<u8> = model.iter().copied().collect();
                    prop_assert_eq!(sorted(from_iter),
                                    sorted(std_heap.iter().copied().collect()));
                }

                #[test]
                fn test_into_vec(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_heap) = build(&elements);
                    let m = model.into_vec();
                    prop_assert_eq!(sorted(m.as_slice().to_vec()),
                                    sorted(std_heap.into_vec()));
                }

                #[test]
                fn test_into_sorted_vec(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_heap) = build(&elements);
                    let m = model.into_sorted_vec();
                    let expected = std_heap.into_sorted_vec();
                    prop_assert_eq!(m.as_slice(), expected.as_slice());
                }

                #[test]
                fn test_append(a in prop::collection::vec(any::<u8>(), 0..20),
                               b in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model_a, mut std_a) = build(&a);
                    let (mut model_b, mut std_b) = build(&b);
                    model_a.append(&mut model_b);
                    std_a.append(&mut std_b);
                    prop_assert_eq!(model_b.len(), std_b.len());
                    prop_assert_eq!(drain_model(model_a), drain_std(std_a));
                }

                #[test]
                fn test_retain(elements in prop::collection::vec(any::<u8>(), 0..20),
                               t in any::<u8>()) {
                    let (mut model, mut std_heap) = build(&elements);
                    model.retain(|x| *x < t);
                    std_heap.retain(|x| *x < t);
                    prop_assert_eq!(drain_model(model), drain_std(std_heap));
                }

                #[test]
                fn test_capacity_ops_preserve_contents(
                    elements in prop::collection::vec(any::<u8>(), 0..20), n in 0usize..40) {
                    let (mut model, mut std_heap) = build(&elements);
                    model.reserve(n);
                    std_heap.reserve(n);
                    model.reserve_exact(n);
                    std_heap.reserve_exact(n);
                    model.shrink_to(n);
                    std_heap.shrink_to(n);
                    model.shrink_to_fit();
                    std_heap.shrink_to_fit();
                    prop_assert!(model.try_reserve(n).is_ok());
                    prop_assert!(model.try_reserve_exact(n).is_ok());
                    prop_assert!(std_heap.try_reserve(n).is_ok());
                    prop_assert!(std_heap.try_reserve_exact(n).is_ok());
                    prop_assert_eq!(drain_model(model), drain_std(std_heap));
                }

                #[test]
                fn test_with_capacity_is_empty(n in 0usize..40) {
                    let model = Model::<u8>::with_capacity(n);
                    let std_heap = Std::<u8>::with_capacity(n);
                    prop_assert_eq!(model.len(), std_heap.len());
                    prop_assert!(model.is_empty());
                }

                #[test]
                fn test_push_pop(elements in prop::collection::vec(any::<u8>(), 1..20)) {
                    let mut model = super::BinaryHeap::<u8, crate::alloc::Global>::new();
                    let mut std_heap = std::collections::BinaryHeap::new();
                    for &e in &elements {
                        model.push(e);
                        std_heap.push(e);
                    }
                    prop_assert_eq!(model.len(), std_heap.len());

                    loop {
                        let model_val = model.pop();
                        let std_val = std_heap.pop();
                        prop_assert_eq!(model_val, std_val);
                        if model_val.is_none() {
                            break;
                        }
                    }
                }

                #[test]
                fn test_peek(elements in prop::collection::vec(any::<u8>(), 1..20)) {
                    let mut model = super::BinaryHeap::<u8, crate::alloc::Global>::new();
                    let mut std_heap = std::collections::BinaryHeap::new();
                    for &e in &elements {
                        model.push(e);
                        std_heap.push(e);
                    }
                    prop_assert_eq!(model.peek().copied(), std_heap.peek().copied());
                }
            }

            #[test]
            fn test_new() {
                let mut model = super::BinaryHeap::<u8, crate::alloc::Global>::new();
                let mut std_heap = std::collections::BinaryHeap::<u8>::new();
                assert_eq!(model.len(), std_heap.len());
                assert_eq!(model.pop(), std_heap.pop());
            }

            // `new_in`/`with_capacity_in` are unstable in std
            // (`allocator_api`), so the expectation — an empty heap — is pinned
            // here.
            #[test]
            fn test_new_in() {
                let model = Model::<u8>::new_in(crate::alloc::Global);
                assert!(model.is_empty());
            }

            #[test]
            fn test_with_capacity_in() {
                let model = Model::<u8>::with_capacity_in(10, crate::alloc::Global);
                assert!(model.is_empty());
            }
        }
    }
    mod btree {
        use rust_primitives::sequence::*;

        /// Index of the first element of the *sorted* `s` that is not `Less`
        /// than `key`, plus whether that element compares `Equal`. Every lookup
        /// in the sorted-`Seq` model of `BTreeSet`/`BTreeMap` is built from
        /// this, so the linear scan lives in one place.
        fn seq_lower_bound<T: Ord>(s: &Seq<T>, key: &T) -> (usize, bool) {
            let l = seq_len(s);
            let mut pos = l;
            let mut eq = false;
            let mut done = false;
            for i in 0..l {
                if !done {
                    let o = seq_index(s, i).cmp(key);
                    if !o.is_lt() {
                        pos = i;
                        eq = o.is_eq();
                        done = true
                    }
                }
            }
            (pos, eq)
        }

        /// `seq_lower_bound` against a *borrowed* key, as std's `BTreeSet`
        /// lookups take. Spelled out separately rather than as the general case
        /// so that the methods which do not need a `Borrow` bound (`insert`,
        /// the set operations, …) do not have to carry one — the model has no
        /// blanket `impl<T> Borrow<T> for T`.
        fn seq_lower_bound_borrowed<T, Q>(s: &Seq<T>, key: &Q) -> (usize, bool)
        where
            T: core::borrow::Borrow<Q> + Ord,
            Q: Ord + ?Sized,
        {
            let l = seq_len(s);
            let mut pos = l;
            let mut eq = false;
            let mut done = false;
            for i in 0..l {
                if !done {
                    let o = seq_index(s, i).borrow().cmp(key);
                    if !o.is_lt() {
                        pos = i;
                        eq = o.is_eq();
                        done = true
                    }
                }
            }
            (pos, eq)
        }

        /// `seq_lower_bound` over a `Seq` of key/value pairs, comparing keys.
        fn seq_lower_bound_key<K: Ord, V>(s: &Seq<(K, V)>, key: &K) -> (usize, bool) {
            let l = seq_len(s);
            let mut pos = l;
            let mut eq = false;
            let mut done = false;
            for i in 0..l {
                if !done {
                    let o = seq_index(s, i).0.cmp(key);
                    if !o.is_lt() {
                        pos = i;
                        eq = o.is_eq();
                        done = true
                    }
                }
            }
            (pos, eq)
        }

        /// `seq_lower_bound_key` against a borrowed key (see
        /// `seq_lower_bound_borrowed` for why this is a separate function).
        fn seq_lower_bound_key_borrowed<K, V, Q>(s: &Seq<(K, V)>, key: &Q) -> (usize, bool)
        where
            K: core::borrow::Borrow<Q> + Ord,
            Q: Ord + ?Sized,
        {
            let l = seq_len(s);
            let mut pos = l;
            let mut eq = false;
            let mut done = false;
            for i in 0..l {
                if !done {
                    let o = seq_index(s, i).0.borrow().cmp(key);
                    if !o.is_lt() {
                        pos = i;
                        eq = o.is_eq();
                        done = true
                    }
                }
            }
            (pos, eq)
        }

        /// Insert `value` at `index`, shifting the tail right (see the same
        /// helper in `vec_deque`).
        #[hax_lib::requires(index <= seq_len(s) && seq_len(s) < core::primitive::usize::MAX)]
        fn seq_insert<T>(s: &mut Seq<T>, index: usize, value: T) {
            let l = seq_len(s);
            let mut right = seq_drain(s, index, l);
            seq_push(s, value);
            seq_concat(s, &mut right)
        }

        /// Model of `alloc::collections::btree::map`.
        ///
        /// DEVIATION(std): a `Seq` of key/value pairs sorted by key, not a
        /// B-tree. Like the `set` model this is a *specification* of the
        /// ordered-map semantics — every lookup is a linear scan — and it
        /// reproduces std's observable behaviour, including that `insert` keeps
        /// the *old* key and replaces only the value.
        mod map {
            use super::{seq_insert, seq_lower_bound_key, seq_lower_bound_key_borrowed};
            use rust_primitives::sequence::*;
            use std::marker::PhantomData;

            #[cfg_attr(test, derive(PartialEq, Debug))]
            pub struct BTreeMap<K, V, A>(pub Seq<(K, V)>, PhantomData<A>);

            /// See [`std::collections::btree_map::UnorderedKeyError`]: the error
            /// `CursorMut::insert_before`/`insert_after` return. The cursor API
            /// itself is not modeled, so nothing here produces one.
            #[cfg_attr(test, derive(PartialEq, Debug))]
            pub struct UnorderedKeyError;

            /// See [`std::collections::btree_map::Iter`]
            pub struct Iter<'a, K, V>(pub Seq<&'a (K, V)>);
            /// See [`std::collections::btree_map::Keys`]
            pub struct Keys<'a, K, V>(pub Seq<&'a K>, PhantomData<&'a V>);
            /// See [`std::collections::btree_map::Values`]
            pub struct Values<'a, K, V>(pub Seq<&'a V>, PhantomData<&'a K>);
            /// See [`std::collections::btree_map::IntoKeys`]
            pub struct IntoKeys<K, V, A>(pub Seq<(K, V)>, PhantomData<A>);
            /// See [`std::collections::btree_map::IntoValues`]
            pub struct IntoValues<K, V, A>(pub Seq<(K, V)>, PhantomData<A>);

            impl<'a, K, V> Iterator for Iter<'a, K, V> {
                type Item = (&'a K, &'a V);
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        let p = seq_remove(&mut self.0, 0);
                        Some((&p.0, &p.1))
                    }
                }
            }
            impl<'a, K, V> Iterator for Keys<'a, K, V> {
                type Item = &'a K;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<'a, K, V> Iterator for Values<'a, K, V> {
                type Item = &'a V;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<K, V, A> Iterator for IntoKeys<K, V, A> {
                type Item = K;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0).0)
                    }
                }
            }
            impl<K, V, A> Iterator for IntoValues<K, V, A> {
                type Item = V;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0).1)
                    }
                }
            }

            // Padding impls, as in `set`: real `alloc` puts eighteen impls (the
            // `Drop`/`Clone`/`Debug`/`Default` boilerplate of `BTreeMap` and of
            // its seven iterator types) before `impl<K, V> BTreeMap<K, V>`, so
            // hax derives `impl_18__new`, `impl_19__clear`/`new_in` and
            // `impl_20__insert` from those positions. Thirteen here, because
            // hax counts the five `Iterator` impls above too. As in `set`, the
            // count is calibrated against what hax emits.
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}

            impl<K, V> BTreeMap<K, V, crate::alloc::Global> {
                /// See [`std::collections::BTreeMap::new`]
                fn new() -> BTreeMap<K, V, crate::alloc::Global> {
                    BTreeMap(seq_empty(), PhantomData)
                }
            }

            // `A: Clone` mirrors std's `impl<K, V, A: Allocator + Clone>`; see
            // the same comment on `set`'s block for why the `Allocator` half is
            // left out and the `Clone` half cannot be.
            impl<K, V, A: Clone> BTreeMap<K, V, A> {
                /// See [`std::collections::BTreeMap::clear`]
                fn clear(&mut self) {
                    self.0 = seq_empty()
                }
                /// See [`std::collections::BTreeMap::new_in`]
                fn new_in(_alloc: A) -> BTreeMap<K, V, A> {
                    BTreeMap(seq_empty(), PhantomData)
                }
            }

            impl<K, V, A: Clone> BTreeMap<K, V, A> {
                /// See [`std::collections::BTreeMap::get`]
                fn get<Q>(&self, key: &Q) -> Option<&V>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_key_borrowed(&self.0, key);
                    if probe.1 {
                        Some(&seq_index(&self.0, probe.0).1)
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::get_key_value`]
                fn get_key_value<Q>(&self, k: &Q) -> Option<(&K, &V)>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_key_borrowed(&self.0, k);
                    if probe.1 {
                        let entry = seq_index(&self.0, probe.0);
                        Some((&entry.0, &entry.1))
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::get_mut`]. Lean-only,
                /// like `VecDeque`'s `_mut` accessors — see the note there.
                #[cfg(not(hax_backend_fstar))]
                fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_key_borrowed(&self.0, key);
                    if probe.1 {
                        Some(&mut seq_index_mut(&mut self.0, probe.0).1)
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::contains_key`]
                fn contains_key<Q>(&self, key: &Q) -> bool
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    seq_lower_bound_key_borrowed(&self.0, key).1
                }
                /// See [`std::collections::BTreeMap::first_key_value`]
                fn first_key_value(&self) -> Option<(&K, &V)>
                where
                    K: Ord,
                {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        let entry = seq_index(&self.0, 0);
                        Some((&entry.0, &entry.1))
                    }
                }
                /// See [`std::collections::BTreeMap::last_key_value`]
                fn last_key_value(&self) -> Option<(&K, &V)>
                where
                    K: Ord,
                {
                    let l = seq_len(&self.0);
                    if l == 0 {
                        None
                    } else {
                        let entry = seq_index(&self.0, l - 1);
                        Some((&entry.0, &entry.1))
                    }
                }
                /// See [`std::collections::BTreeMap::pop_first`]
                fn pop_first(&mut self) -> Option<(K, V)>
                where
                    K: Ord,
                {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
                /// See [`std::collections::BTreeMap::pop_last`]
                fn pop_last(&mut self) -> Option<(K, V)>
                where
                    K: Ord,
                {
                    let l = seq_len(&self.0);
                    if l == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, l - 1))
                    }
                }
                /// See [`std::collections::BTreeMap::insert`]: on a key that is
                /// already present the *value* is replaced and the old one
                /// returned; the stored key is left alone, as in std.
                ///
                /// No `#[hax_lib::requires]` on the length here: that would need
                /// `#[hax_lib::attributes]` on the block, which moves it to the
                /// end of hax's impl numbering and so off index 20. `seq_insert`
                /// carries the bound instead.
                fn insert(&mut self, key: K, value: V) -> Option<V>
                where
                    K: Ord,
                {
                    let probe = seq_lower_bound_key(&self.0, &key);
                    if probe.1 {
                        let old = seq_remove(&mut self.0, probe.0);
                        seq_insert(&mut self.0, probe.0, (old.0, value));
                        Some(old.1)
                    } else {
                        seq_insert(&mut self.0, probe.0, (key, value));
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::remove`]
                fn remove<Q>(&mut self, key: &Q) -> Option<V>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_key_borrowed(&self.0, key);
                    if probe.1 {
                        Some(seq_remove(&mut self.0, probe.0).1)
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::remove_entry`]
                fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_key_borrowed(&self.0, key);
                    if probe.1 {
                        Some(seq_remove(&mut self.0, probe.0))
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeMap::append`]: on a shared key
                /// the value from `other` wins.
                fn append(&mut self, other: &mut BTreeMap<K, V, A>)
                where
                    K: Ord,
                    A: Clone,
                {
                    let l = seq_len(&other.0);
                    for _k in 0..l {
                        if seq_len(&other.0) > 0 {
                            let entry = seq_remove(&mut other.0, 0);
                            let _old = self.insert(entry.0, entry.1);
                        }
                    }
                }
                /// See [`std::collections::BTreeMap::split_off`]: keeps the
                /// entries with keys `< key`, returns those `>= key`.
                fn split_off<Q: Ord + ?Sized>(&mut self, key: &Q) -> BTreeMap<K, V, A>
                where
                    K: core::borrow::Borrow<Q> + Ord,
                    A: Clone,
                {
                    let l = seq_len(&self.0);
                    let probe = seq_lower_bound_key_borrowed(&self.0, key);
                    BTreeMap(seq_drain(&mut self.0, probe.0, l), PhantomData::<A>)
                }
                /// See [`std::collections::BTreeMap::into_keys`]
                fn into_keys(self) -> IntoKeys<K, V, A> {
                    IntoKeys(self.0, PhantomData::<A>)
                }
                /// See [`std::collections::BTreeMap::into_values`]
                fn into_values(self) -> IntoValues<K, V, A> {
                    IntoValues(self.0, PhantomData::<A>)
                }
            }

            // Real `alloc` has a second batch of iterator/comparison impls
            // between the block above and the one below, which is why `len`,
            // `is_empty`, `iter`, `keys` and `values` sit at impl index 92
            // rather than 21. Padding again, same calibration.
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}
            impl BTreeMap<(), (), ()> {}

            impl<K, V, A: Clone> BTreeMap<K, V, A> {
                /// See [`std::collections::BTreeMap::len`]
                fn len(&self) -> usize {
                    seq_len(&self.0)
                }
                /// See [`std::collections::BTreeMap::is_empty`]
                fn is_empty(&self) -> bool {
                    seq_len(&self.0) == 0
                }
                /// See [`std::collections::BTreeMap::iter`]
                fn iter(&self) -> Iter<'_, K, V> {
                    Iter(seq_from_slice(seq_to_slice(&self.0)))
                }
                /// See [`std::collections::BTreeMap::keys`]
                fn keys(&self) -> Keys<'_, K, V> {
                    let mut out = seq_empty();
                    for i in 0..seq_len(&self.0) {
                        seq_push(&mut out, &seq_index(&self.0, i).0)
                    }
                    Keys(out, PhantomData)
                }
                /// See [`std::collections::BTreeMap::values`]
                fn values(&self) -> Values<'_, K, V> {
                    let mut out = seq_empty();
                    for i in 0..seq_len(&self.0) {
                        seq_push(&mut out, &seq_index(&self.0, i).1)
                    }
                    Values(out, PhantomData)
                }
            }

            #[cfg(test)]
            mod tests {
                use crate::testing::Inject;
                use proptest::prelude::*;

                type Model<K, V> = super::BTreeMap<K, V, crate::alloc::Global>;
                type Std<K, V> = std::collections::BTreeMap<K, V>;

                impl<K: Clone + Ord, V: Clone> Inject for Std<K, V> {
                    type Model = Model<K, V>;
                    fn inject(&self) -> Model<K, V> {
                        let flat: std::vec::Vec<(K, V)> =
                            self.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
                        super::BTreeMap(
                            rust_primitives::sequence::seq_from_boxed_slice(
                                flat.into_boxed_slice(),
                            ),
                            std::marker::PhantomData,
                        )
                    }
                }

                fn build(entries: &[(u8, u8)]) -> (Model<u8, u8>, Std<u8, u8>) {
                    let mut model = Model::new();
                    let mut std_map = Std::new();
                    for &(k, v) in entries {
                        model.insert(k, v);
                        std_map.insert(k, v);
                    }
                    (model, std_map)
                }

                fn entries() -> impl Strategy<Value = std::vec::Vec<(u8, u8)>> {
                    prop::collection::vec((0u8..8, any::<u8>()), 0..20)
                }

                proptest! {
                    #[test]
                    fn test_insert_returns_old_value(es in entries()) {
                        let mut model = Model::new();
                        let mut std_map = Std::new();
                        for &(k, v) in &es {
                            prop_assert_eq!(model.insert(k, v), std_map.insert(k, v));
                        }
                        prop_assert_eq!(model, std_map.inject());
                    }

                    #[test]
                    fn test_len_is_empty(es in entries()) {
                        let (model, std_map) = build(&es);
                        prop_assert_eq!(model.len(), std_map.len());
                        prop_assert_eq!(model.is_empty(), std_map.is_empty());
                    }

                    #[test]
                    fn test_get(es in entries(), k in 0u8..10) {
                        let (model, std_map) = build(&es);
                        prop_assert_eq!(model.get(&k), std_map.get(&k));
                    }

                    #[test]
                    fn test_get_key_value(es in entries(), k in 0u8..10) {
                        let (model, std_map) = build(&es);
                        prop_assert_eq!(model.get_key_value(&k), std_map.get_key_value(&k));
                    }

                    #[cfg(not(hax_backend_fstar))]
                    #[test]
                    fn test_get_mut(es in entries(), k in 0u8..10, v in any::<u8>()) {
                        let (mut model, mut std_map) = build(&es);
                        prop_assert_eq!(model.get_mut(&k).copied(), std_map.get_mut(&k).copied());
                        if let Some(m) = model.get_mut(&k) {
                            *m = v
                        }
                        if let Some(sm) = std_map.get_mut(&k) {
                            *sm = v
                        }
                        prop_assert_eq!(model, std_map.inject());
                    }

                    #[test]
                    fn test_contains_key(es in entries(), k in 0u8..10) {
                        let (model, std_map) = build(&es);
                        prop_assert_eq!(model.contains_key(&k), std_map.contains_key(&k));
                    }

                    #[test]
                    fn test_first_last_key_value(es in entries()) {
                        let (model, std_map) = build(&es);
                        prop_assert_eq!(model.first_key_value(), std_map.first_key_value());
                        prop_assert_eq!(model.last_key_value(), std_map.last_key_value());
                    }

                    #[test]
                    fn test_pop_first(es in entries()) {
                        let (mut model, mut std_map) = build(&es);
                        for _ in 0..=es.len() {
                            prop_assert_eq!(model.pop_first(), std_map.pop_first());
                            prop_assert_eq!(&model, &std_map.inject());
                        }
                    }

                    #[test]
                    fn test_pop_last(es in entries()) {
                        let (mut model, mut std_map) = build(&es);
                        for _ in 0..=es.len() {
                            prop_assert_eq!(model.pop_last(), std_map.pop_last());
                            prop_assert_eq!(&model, &std_map.inject());
                        }
                    }

                    #[test]
                    fn test_remove(es in entries(), k in 0u8..10) {
                        let (mut model, mut std_map) = build(&es);
                        prop_assert_eq!(model.remove(&k), std_map.remove(&k));
                        prop_assert_eq!(model, std_map.inject());
                    }

                    #[test]
                    fn test_remove_entry(es in entries(), k in 0u8..10) {
                        let (mut model, mut std_map) = build(&es);
                        prop_assert_eq!(model.remove_entry(&k), std_map.remove_entry(&k));
                        prop_assert_eq!(model, std_map.inject());
                    }

                    #[test]
                    fn test_clear(es in entries()) {
                        let (mut model, mut std_map) = build(&es);
                        model.clear();
                        std_map.clear();
                        prop_assert_eq!(model, std_map.inject());
                    }

                    #[test]
                    fn test_append(a in entries(), b in entries()) {
                        let (mut model_a, mut std_a) = build(&a);
                        let (mut model_b, mut std_b) = build(&b);
                        model_a.append(&mut model_b);
                        std_a.append(&mut std_b);
                        prop_assert_eq!(model_a, std_a.inject());
                        prop_assert_eq!(model_b, std_b.inject());
                    }

                    #[test]
                    fn test_split_off(es in entries(), k in 0u8..10) {
                        let (mut model, mut std_map) = build(&es);
                        let model_tail = model.split_off(&k);
                        let std_tail = std_map.split_off(&k);
                        prop_assert_eq!(model, std_map.inject());
                        prop_assert_eq!(model_tail, std_tail.inject());
                    }

                    #[test]
                    fn test_iter(es in entries()) {
                        let (model, std_map) = build(&es);
                        let m: std::vec::Vec<(u8, u8)> =
                            model.iter().map(|(k, v)| (*k, *v)).collect();
                        let s: std::vec::Vec<(u8, u8)> =
                            std_map.iter().map(|(k, v)| (*k, *v)).collect();
                        prop_assert_eq!(m, s);
                    }

                    #[test]
                    fn test_keys_values(es in entries()) {
                        let (model, std_map) = build(&es);
                        let mk: std::vec::Vec<u8> = model.keys().copied().collect();
                        let sk: std::vec::Vec<u8> = std_map.keys().copied().collect();
                        prop_assert_eq!(mk, sk);
                        let mv: std::vec::Vec<u8> = model.values().copied().collect();
                        let sv: std::vec::Vec<u8> = std_map.values().copied().collect();
                        prop_assert_eq!(mv, sv);
                    }

                    #[test]
                    fn test_into_keys_values(es in entries()) {
                        let (model, std_map) = build(&es);
                        let mk: std::vec::Vec<u8> = model.into_keys().collect();
                        let sk: std::vec::Vec<u8> = std_map.clone().into_keys().collect();
                        prop_assert_eq!(mk, sk);
                        let (model, std_map) = build(&es);
                        let mv: std::vec::Vec<u8> = model.into_values().collect();
                        let sv: std::vec::Vec<u8> = std_map.into_values().collect();
                        prop_assert_eq!(mv, sv);
                    }
                }

                #[test]
                fn test_new() {
                    let model = Model::<u8, u8>::new();
                    assert!(model.is_empty());
                    assert_eq!(model.len(), 0);
                }

                // `new_in` is unstable in std (`btreemap_alloc`), so the
                // expectation — an empty map — is pinned here.
                #[test]
                fn test_new_in() {
                    let model = Model::<u8, u8>::new_in(crate::alloc::Global);
                    assert!(model.is_empty());
                }

                #[test]
                fn test_unordered_key_error_is_a_unit_struct() {
                    // Nothing in the model produces one; this only pins that the
                    // type exists and is inhabited.
                    let _e = super::UnorderedKeyError;
                }
            }
        }

        /// Model of `alloc::collections::btree::set`.
        ///
        /// DEVIATION(std): a sorted, duplicate-free `Seq`, not a B-tree. This is
        /// a *specification* of `BTreeSet`'s ordered-set semantics, not a
        /// performant implementation — every lookup is a linear scan. All the
        /// observable behaviour (element order, which of two equal elements is
        /// kept, iteration order) matches std.
        mod set {
            use super::{seq_insert, seq_lower_bound, seq_lower_bound_borrowed};
            use hax_lib::ToInt;
            use rust_primitives::sequence::*;
            use std::marker::PhantomData;

            #[cfg_attr(test, derive(PartialEq, Debug))]
            pub struct BTreeSet<T, A>(pub Seq<T>, PhantomData<A>);

            /// See [`std::collections::btree_set::Iter`]
            pub struct Iter<'a, T>(pub Seq<&'a T>);
            /// See [`std::collections::btree_set::Difference`]
            pub struct Difference<'a, T, A>(pub Seq<&'a T>, PhantomData<A>);
            /// See [`std::collections::btree_set::Intersection`]
            pub struct Intersection<'a, T, A>(pub Seq<&'a T>, PhantomData<A>);
            /// See [`std::collections::btree_set::Union`]
            pub struct Union<'a, T>(pub Seq<&'a T>);
            /// See [`std::collections::btree_set::SymmetricDifference`]
            pub struct SymmetricDifference<'a, T>(pub Seq<&'a T>);

            impl<'a, T> Iterator for Iter<'a, T> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<'a, T, A> Iterator for Difference<'a, T, A> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<'a, T, A> Iterator for Intersection<'a, T, A> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<'a, T> Iterator for Union<'a, T> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
            impl<'a, T> Iterator for SymmetricDifference<'a, T> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }

            // Padding impls, as in `vec_deque`/`linked_list`: real `alloc` has
            // thirteen impls (the comparison/`Clone`/`Hash` impls plus the
            // iterator `Debug`s) before `impl<T> BTreeSet<T>`, and hax derives
            // `impl_13__new` / `impl_14__insert` from that position. Eight
            // here, because hax counts the five `Iterator` impls above too —
            // which is also why those are written *before* this padding, so
            // that the two `BTreeSet` blocks stay adjacent at 13 and 14. The
            // count is calibrated against what hax emits.
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}

            impl<T> BTreeSet<T, crate::alloc::Global> {
                /// See [`std::collections::BTreeSet::new`]
                fn new() -> BTreeSet<T, crate::alloc::Global> {
                    BTreeSet(seq_empty(), PhantomData)
                }
            }

            // Real `alloc` bounds this block `impl<T, A: Allocator + Clone>`,
            // and the `Clone` half must be mirrored: Aeneas passes a `Clone A`
            // dictionary as the first argument of *every* method here. (The
            // `Allocator` half is deliberately not mirrored — it is a
            // method-less marker trait, which Aeneas erases, and F* resolves it
            // implicitly; `vec_deque` and `linked_list` omit it likewise.)
            #[hax_lib::attributes]
            impl<T, A: Clone> BTreeSet<T, A> {
                /// See [`std::collections::BTreeSet::new_in`]
                fn new_in(_alloc: A) -> BTreeSet<T, A> {
                    BTreeSet(seq_empty(), PhantomData)
                }
                /// See [`std::collections::BTreeSet::len`]
                fn len(&self) -> usize {
                    seq_len(&self.0)
                }
                /// See [`std::collections::BTreeSet::is_empty`]
                fn is_empty(&self) -> bool {
                    seq_len(&self.0) == 0
                }
                /// See [`std::collections::BTreeSet::clear`].
                ///
                /// std repeats `A: Clone` here on top of the block's, and so
                /// must we: the two bounds are two dictionary arguments.
                fn clear(&mut self)
                where
                    A: Clone,
                {
                    self.0 = seq_empty()
                }
                /// See [`std::collections::BTreeSet::first`]
                fn first(&self) -> Option<&T>
                where
                    T: Ord,
                {
                    if self.len() == 0 {
                        None
                    } else {
                        Some(seq_index(&self.0, 0))
                    }
                }
                /// See [`std::collections::BTreeSet::last`]
                fn last(&self) -> Option<&T>
                where
                    T: Ord,
                {
                    let l = self.len();
                    if l == 0 {
                        None
                    } else {
                        Some(seq_index(&self.0, l - 1))
                    }
                }
                /// See [`std::collections::BTreeSet::pop_first`]
                fn pop_first(&mut self) -> Option<T>
                where
                    T: Ord,
                {
                    if self.len() == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
                /// See [`std::collections::BTreeSet::pop_last`]
                fn pop_last(&mut self) -> Option<T>
                where
                    T: Ord,
                {
                    let l = self.len();
                    if l == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, l - 1))
                    }
                }
                /// See [`std::collections::BTreeSet::insert`]: `false` when an
                /// equal element was already present, which is then kept.
                #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
                fn insert(&mut self, value: T) -> bool
                where
                    T: Ord,
                {
                    let probe = seq_lower_bound(&self.0, &value);
                    if probe.1 {
                        false
                    } else {
                        seq_insert(&mut self.0, probe.0, value);
                        true
                    }
                }
                /// See [`std::collections::BTreeSet::replace`]: unlike `insert`,
                /// the *new* element wins and the old one is returned.
                #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
                fn replace(&mut self, value: T) -> Option<T>
                where
                    T: Ord,
                {
                    let probe = seq_lower_bound(&self.0, &value);
                    if probe.1 {
                        let old = seq_remove(&mut self.0, probe.0);
                        seq_insert(&mut self.0, probe.0, value);
                        Some(old)
                    } else {
                        seq_insert(&mut self.0, probe.0, value);
                        None
                    }
                }
                /// See [`std::collections::BTreeSet::contains`]
                fn contains<Q>(&self, value: &Q) -> bool
                where
                    T: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    seq_lower_bound_borrowed(&self.0, value).1
                }
                /// See [`std::collections::BTreeSet::get`]
                fn get<Q>(&self, value: &Q) -> Option<&T>
                where
                    T: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_borrowed(&self.0, value);
                    if probe.1 {
                        Some(seq_index(&self.0, probe.0))
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeSet::remove`]
                fn remove<Q>(&mut self, value: &Q) -> bool
                where
                    T: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_borrowed(&self.0, value);
                    if probe.1 {
                        let _removed = seq_remove(&mut self.0, probe.0);
                        true
                    } else {
                        false
                    }
                }
                /// See [`std::collections::BTreeSet::take`]
                fn take<Q>(&mut self, value: &Q) -> Option<T>
                where
                    T: core::borrow::Borrow<Q> + Ord,
                    Q: Ord + ?Sized,
                {
                    let probe = seq_lower_bound_borrowed(&self.0, value);
                    if probe.1 {
                        Some(seq_remove(&mut self.0, probe.0))
                    } else {
                        None
                    }
                }
                /// See [`std::collections::BTreeSet::split_off`]: keeps the
                /// elements `< value`, returns those `>= value`.
                fn split_off<Q: Ord + ?Sized>(&mut self, value: &Q) -> BTreeSet<T, A>
                where
                    T: core::borrow::Borrow<Q> + Ord,
                    A: Clone,
                {
                    let l = self.len();
                    let probe = seq_lower_bound_borrowed(&self.0, value);
                    BTreeSet(seq_drain(&mut self.0, probe.0, l), PhantomData::<A>)
                }
                /// See [`std::collections::BTreeSet::append`]: elements from
                /// `other` win over equal ones already in `self`.
                fn append(&mut self, other: &mut BTreeSet<T, A>)
                where
                    T: Ord,
                    A: Clone,
                {
                    let l = other.len();
                    for _k in 0..l {
                        if other.len() > 0 {
                            let x = seq_remove(&mut other.0, 0);
                            let _old = self.replace(x);
                        }
                    }
                }
                /// See [`std::collections::BTreeSet::retain`]. `FnMut` is
                /// std's bound and has to be matched — see the note on
                /// `VecDeque::retain`.
                fn retain<F>(&mut self, mut f: F)
                where
                    T: Ord,
                    F: FnMut(&T) -> bool,
                {
                    let l = self.len();
                    for k in 0..l {
                        // Not in the Lean lane: aeneas translates the invariant into `hax_lib`
                        // items the Lean library does not define.
                        #[cfg(not(charon))]
                        hax_lib::loop_invariant!(
                            |k: usize| seq_len(&self.0).to_int() + k.to_int() >= l.to_int()
                        );
                        let i = l - 1 - k;
                        if !f(seq_index(&self.0, i)) {
                            let _removed = seq_remove(&mut self.0, i);
                        }
                    }
                }
                /// See [`std::collections::BTreeSet::iter`]
                fn iter(&self) -> Iter<'_, T> {
                    Iter(seq_from_slice(seq_to_slice(&self.0)))
                }
                /// See [`std::collections::BTreeSet::is_subset`]
                fn is_subset(&self, other: &BTreeSet<T, A>) -> bool
                where
                    T: Ord,
                {
                    let mut res = true;
                    for i in 0..self.len() {
                        if !seq_lower_bound(&other.0, seq_index(&self.0, i)).1 {
                            res = false
                        }
                    }
                    res
                }
                /// See [`std::collections::BTreeSet::is_superset`]
                fn is_superset(&self, other: &BTreeSet<T, A>) -> bool
                where
                    T: Ord,
                {
                    other.is_subset(self)
                }
                /// See [`std::collections::BTreeSet::is_disjoint`]
                fn is_disjoint(&self, other: &BTreeSet<T, A>) -> bool
                where
                    T: Ord,
                {
                    let mut res = true;
                    for i in 0..self.len() {
                        if seq_lower_bound(&other.0, seq_index(&self.0, i)).1 {
                            res = false
                        }
                    }
                    res
                }
                /// See [`std::collections::BTreeSet::difference`]
                fn difference<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Difference<'a, T, A>
                where
                    T: Ord,
                {
                    let mut out = seq_empty();
                    for i in 0..self.len() {
                        let x = seq_index(&self.0, i);
                        if !seq_lower_bound(&other.0, x).1 {
                            seq_push(&mut out, x)
                        }
                    }
                    Difference(out, PhantomData::<A>)
                }
                /// See [`std::collections::BTreeSet::intersection`]
                fn intersection<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Intersection<'a, T, A>
                where
                    T: Ord,
                {
                    let mut out = seq_empty();
                    for i in 0..self.len() {
                        let x = seq_index(&self.0, i);
                        if seq_lower_bound(&other.0, x).1 {
                            seq_push(&mut out, x)
                        }
                    }
                    Intersection(out, PhantomData::<A>)
                }
                /// See [`std::collections::BTreeSet::union`]: ascending, each
                /// element once, `self`'s copy on a tie (as std does).
                fn union<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Union<'a, T>
                where
                    T: Ord,
                {
                    let mut out = seq_empty();
                    let mut i = 0;
                    let mut j = 0;
                    while i < self.len() || j < other.len() {
                        if i >= self.len() {
                            seq_push(&mut out, seq_index(&other.0, j));
                            j += 1
                        } else if j >= other.len() {
                            seq_push(&mut out, seq_index(&self.0, i));
                            i += 1
                        } else {
                            let a = seq_index(&self.0, i);
                            let b = seq_index(&other.0, j);
                            let o = a.cmp(b);
                            if o.is_lt() {
                                seq_push(&mut out, a);
                                i += 1
                            } else if o.is_gt() {
                                seq_push(&mut out, b);
                                j += 1
                            } else {
                                seq_push(&mut out, a);
                                i += 1;
                                j += 1
                            }
                        }
                    }
                    Union(out)
                }
                /// See [`std::collections::BTreeSet::symmetric_difference`]
                fn symmetric_difference<'a>(
                    &'a self,
                    other: &'a BTreeSet<T, A>,
                ) -> SymmetricDifference<'a, T>
                where
                    T: Ord,
                {
                    let mut out = seq_empty();
                    let mut i = 0;
                    let mut j = 0;
                    while i < self.len() || j < other.len() {
                        if i >= self.len() {
                            seq_push(&mut out, seq_index(&other.0, j));
                            j += 1
                        } else if j >= other.len() {
                            seq_push(&mut out, seq_index(&self.0, i));
                            i += 1
                        } else {
                            let a = seq_index(&self.0, i);
                            let b = seq_index(&other.0, j);
                            let o = a.cmp(b);
                            if o.is_lt() {
                                seq_push(&mut out, a);
                                i += 1
                            } else if o.is_gt() {
                                seq_push(&mut out, b);
                                j += 1
                            } else {
                                i += 1;
                                j += 1
                            }
                        }
                    }
                    SymmetricDifference(out)
                }
            }

            #[cfg(test)]
            mod tests {
                use crate::testing::Inject;
                use proptest::prelude::*;

                type Model<T> = super::BTreeSet<T, crate::alloc::Global>;
                type Std<T> = std::collections::BTreeSet<T>;

                impl<T: Clone + Ord> Inject for Std<T> {
                    type Model = Model<T>;
                    fn inject(&self) -> Model<T> {
                        let flat: std::vec::Vec<T> = self.iter().cloned().collect();
                        super::BTreeSet(
                            rust_primitives::sequence::seq_from_boxed_slice(
                                flat.into_boxed_slice(),
                            ),
                            std::marker::PhantomData,
                        )
                    }
                }

                fn build(elements: &[u8]) -> (Model<u8>, Std<u8>) {
                    let mut model = Model::new();
                    let mut std_set = Std::new();
                    for &e in elements {
                        model.insert(e);
                        std_set.insert(e);
                    }
                    (model, std_set)
                }

                proptest! {
                    #[test]
                    fn test_insert_dedups_and_sorts(
                        elements in prop::collection::vec(0u8..8, 0..20)) {
                        let mut model = Model::new();
                        let mut std_set = Std::new();
                        for &e in &elements {
                            prop_assert_eq!(model.insert(e), std_set.insert(e));
                        }
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_len_is_empty(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (model, std_set) = build(&elements);
                        prop_assert_eq!(model.len(), std_set.len());
                        prop_assert_eq!(model.is_empty(), std_set.is_empty());
                    }

                    #[test]
                    fn test_contains(elements in prop::collection::vec(0u8..8, 0..20),
                                     x in 0u8..10) {
                        let (model, std_set) = build(&elements);
                        prop_assert_eq!(model.contains(&x), std_set.contains(&x));
                    }

                    #[test]
                    fn test_get(elements in prop::collection::vec(0u8..8, 0..20), x in 0u8..10) {
                        let (model, std_set) = build(&elements);
                        prop_assert_eq!(model.get(&x), std_set.get(&x));
                    }

                    #[test]
                    fn test_remove(elements in prop::collection::vec(0u8..8, 0..20), x in 0u8..10) {
                        let (mut model, mut std_set) = build(&elements);
                        prop_assert_eq!(model.remove(&x), std_set.remove(&x));
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_take(elements in prop::collection::vec(0u8..8, 0..20), x in 0u8..10) {
                        let (mut model, mut std_set) = build(&elements);
                        prop_assert_eq!(model.take(&x), std_set.take(&x));
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_replace(elements in prop::collection::vec(0u8..8, 0..20),
                                    x in 0u8..10) {
                        let (mut model, mut std_set) = build(&elements);
                        prop_assert_eq!(model.replace(x), std_set.replace(x));
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_first_last(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (model, std_set) = build(&elements);
                        prop_assert_eq!(model.first(), std_set.first());
                        prop_assert_eq!(model.last(), std_set.last());
                    }

                    #[test]
                    fn test_pop_first(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (mut model, mut std_set) = build(&elements);
                        for _ in 0..=elements.len() {
                            prop_assert_eq!(model.pop_first(), std_set.pop_first());
                            prop_assert_eq!(&model, &std_set.inject());
                        }
                    }

                    #[test]
                    fn test_pop_last(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (mut model, mut std_set) = build(&elements);
                        for _ in 0..=elements.len() {
                            prop_assert_eq!(model.pop_last(), std_set.pop_last());
                            prop_assert_eq!(&model, &std_set.inject());
                        }
                    }

                    #[test]
                    fn test_clear(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (mut model, mut std_set) = build(&elements);
                        model.clear();
                        std_set.clear();
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_append(a in prop::collection::vec(0u8..8, 0..20),
                                   b in prop::collection::vec(0u8..8, 0..20)) {
                        let (mut model_a, mut std_a) = build(&a);
                        let (mut model_b, mut std_b) = build(&b);
                        model_a.append(&mut model_b);
                        std_a.append(&mut std_b);
                        prop_assert_eq!(model_a, std_a.inject());
                        prop_assert_eq!(model_b, std_b.inject());
                    }

                    #[test]
                    fn test_split_off(elements in prop::collection::vec(0u8..8, 0..20),
                                      at in 0u8..10) {
                        let (mut model, mut std_set) = build(&elements);
                        let model_tail = model.split_off(&at);
                        let std_tail = std_set.split_off(&at);
                        prop_assert_eq!(model, std_set.inject());
                        prop_assert_eq!(model_tail, std_tail.inject());
                    }

                    #[test]
                    fn test_retain(elements in prop::collection::vec(0u8..8, 0..20), t in 0u8..10) {
                        let (mut model, mut std_set) = build(&elements);
                        model.retain(|x| *x < t);
                        std_set.retain(|x| *x < t);
                        prop_assert_eq!(model, std_set.inject());
                    }

                    #[test]
                    fn test_iter(elements in prop::collection::vec(0u8..8, 0..20)) {
                        let (model, std_set) = build(&elements);
                        let from_model: std::vec::Vec<u8> = model.iter().copied().collect();
                        let from_std: std::vec::Vec<u8> = std_set.iter().copied().collect();
                        prop_assert_eq!(from_model, from_std);
                    }

                    #[test]
                    fn test_subset_superset_disjoint(
                        a in prop::collection::vec(0u8..8, 0..12),
                        b in prop::collection::vec(0u8..8, 0..12)) {
                        let (model_a, std_a) = build(&a);
                        let (model_b, std_b) = build(&b);
                        prop_assert_eq!(model_a.is_subset(&model_b), std_a.is_subset(&std_b));
                        prop_assert_eq!(model_a.is_superset(&model_b), std_a.is_superset(&std_b));
                        prop_assert_eq!(model_a.is_disjoint(&model_b), std_a.is_disjoint(&std_b));
                    }

                    #[test]
                    fn test_set_operations(a in prop::collection::vec(0u8..8, 0..12),
                                           b in prop::collection::vec(0u8..8, 0..12)) {
                        let (model_a, std_a) = build(&a);
                        let (model_b, std_b) = build(&b);
                        let m: std::vec::Vec<u8> = model_a.difference(&model_b).copied().collect();
                        let s: std::vec::Vec<u8> = std_a.difference(&std_b).copied().collect();
                        prop_assert_eq!(m, s);
                        let m: std::vec::Vec<u8> =
                            model_a.intersection(&model_b).copied().collect();
                        let s: std::vec::Vec<u8> = std_a.intersection(&std_b).copied().collect();
                        prop_assert_eq!(m, s);
                        let m: std::vec::Vec<u8> = model_a.union(&model_b).copied().collect();
                        let s: std::vec::Vec<u8> = std_a.union(&std_b).copied().collect();
                        prop_assert_eq!(m, s);
                        let m: std::vec::Vec<u8> =
                            model_a.symmetric_difference(&model_b).copied().collect();
                        let s: std::vec::Vec<u8> =
                            std_a.symmetric_difference(&std_b).copied().collect();
                        prop_assert_eq!(m, s);
                    }
                }

                #[test]
                fn test_new() {
                    let model = Model::<u8>::new();
                    assert!(model.is_empty());
                    assert_eq!(model.len(), std::collections::BTreeSet::<u8>::new().len());
                }

                // `new_in` is unstable in std (`btreemap_alloc`), so the
                // expectation — an empty set — is pinned here.
                #[test]
                fn test_new_in() {
                    let model = Model::<u8>::new_in(crate::alloc::Global);
                    assert!(model.is_empty());
                }
            }
        }

        #[cfg(test)]
        mod tests {
            use proptest::prelude::*;

            proptest! {
                #[test]
                fn test_seq_lower_bound(elements in prop::collection::vec(0u8..8, 0..20),
                                        key in 0u8..10) {
                    let mut sorted = elements.clone();
                    sorted.sort();
                    let seq = rust_primitives::sequence::seq_from_boxed_slice(
                        sorted.clone().into_boxed_slice());
                    let (pos, eq) = super::seq_lower_bound(&seq, &key);
                    prop_assert_eq!(pos, sorted.partition_point(|x| *x < key));
                    prop_assert_eq!(eq, sorted.binary_search(&key).is_ok());
                    // The borrowed variant must agree at `Q = T`.
                    prop_assert_eq!(super::seq_lower_bound_borrowed(&seq, &key), (pos, eq));
                }

                #[test]
                fn test_seq_insert(elements in prop::collection::vec(any::<u8>(), 0..20),
                                   at in 0usize..21, x in any::<u8>()) {
                    let at = at % (elements.len() + 1);
                    let mut seq = rust_primitives::sequence::seq_from_boxed_slice(
                        elements.clone().into_boxed_slice());
                    super::seq_insert(&mut seq, at, x);
                    let mut expected = elements.clone();
                    expected.insert(at, x);
                    prop_assert_eq!(
                        rust_primitives::sequence::seq_to_slice(&seq),
                        &expected[..]
                    );
                }
            }
        }
    }
    /// Model of `alloc::collections::linked_list`.
    ///
    /// DEVIATION(std): a `Seq`, not a doubly-linked list. Every observation std
    /// makes about a `LinkedList` is about its element sequence, so the two
    /// agree on the whole non-cursor API; the `Cursor`/`CursorMut` half, which
    /// is the only place the node structure is observable, is not modeled.
    mod linked_list {
        use hax_lib::ToInt;
        use rust_primitives::sequence::*;

        #[cfg_attr(test, derive(PartialEq, Debug))]
        pub struct LinkedList<T, A>(pub Seq<T>, std::marker::PhantomData<A>);

        /// The shared-borrow iterator returned by
        /// [`std::collections::LinkedList::iter`].
        pub struct Iter<'a, T>(pub Seq<&'a T>);

        // Empty impls to line the model's impl numbering up with real
        // `alloc`'s, where four iterator `Debug`/`Clone` impls, `Node`'s
        // inherent block, a private `LinkedList` helper block and `Default`
        // precede the two public inherent blocks (see the same comment in
        // `vec_deque`). Six, not seven, because hax also counts the
        // `Iterator for Iter` impl below ahead of these — the count is
        // calibrated so that hax emits `impl_7__new` / `impl_8__len`, which is
        // what it derives at real-`alloc` call sites.
        impl LinkedList<(), ()> {}
        impl LinkedList<(), ()> {}
        impl LinkedList<(), ()> {}
        impl LinkedList<(), ()> {}
        impl LinkedList<(), ()> {}
        impl LinkedList<(), ()> {}

        #[hax_lib::attributes]
        impl<T> LinkedList<T, crate::alloc::Global> {
            /// See [`std::collections::LinkedList::new`]
            fn new() -> LinkedList<T, crate::alloc::Global> {
                LinkedList(seq_empty(), std::marker::PhantomData)
            }
            /// See [`std::collections::LinkedList::append`]
            #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= core::primitive::usize::MAX.to_int())]
            fn append(&mut self, other: &mut LinkedList<T, crate::alloc::Global>) {
                seq_concat(&mut self.0, &mut other.0);
                other.0 = seq_empty()
            }
        }

        #[hax_lib::attributes]
        impl<T, A> LinkedList<T, A> {
            /// See [`std::collections::LinkedList::new_in`]
            fn new_in(_alloc: A) -> LinkedList<T, A> {
                LinkedList(seq_empty(), std::marker::PhantomData)
            }
            /// See [`std::collections::LinkedList::len`]
            fn len(&self) -> usize {
                seq_len(&self.0)
            }
            /// See [`std::collections::LinkedList::is_empty`]
            fn is_empty(&self) -> bool {
                seq_len(&self.0) == 0
            }
            /// See [`std::collections::LinkedList::clear`]
            fn clear(&mut self) {
                self.0 = seq_empty()
            }
            /// See [`std::collections::LinkedList::front`]
            fn front(&self) -> Option<&T> {
                if self.len() == 0 {
                    None
                } else {
                    Some(seq_index(&self.0, 0))
                }
            }
            /// See [`std::collections::LinkedList::back`]
            fn back(&self) -> Option<&T> {
                let l = self.len();
                if l == 0 {
                    None
                } else {
                    Some(seq_index(&self.0, l - 1))
                }
            }
            /// See [`std::collections::LinkedList::front_mut`]. Lean-only,
            /// like `VecDeque`'s `_mut` accessors — see the note there.
            #[cfg(not(hax_backend_fstar))]
            fn front_mut(&mut self) -> Option<&mut T> {
                if self.len() == 0 {
                    None
                } else {
                    Some(seq_index_mut(&mut self.0, 0))
                }
            }
            /// See [`std::collections::LinkedList::back_mut`]
            #[cfg(not(hax_backend_fstar))]
            fn back_mut(&mut self) -> Option<&mut T> {
                let l = self.len();
                if l == 0 {
                    None
                } else {
                    Some(seq_index_mut(&mut self.0, l - 1))
                }
            }
            /// See [`std::collections::LinkedList::push_front_mut`]
            #[cfg(not(hax_backend_fstar))]
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push_front_mut(&mut self, elt: T) -> &mut T {
                self.push_front(elt);
                seq_index_mut(&mut self.0, 0)
            }
            /// See [`std::collections::LinkedList::push_back_mut`]
            #[cfg(not(hax_backend_fstar))]
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push_back_mut(&mut self, elt: T) -> &mut T {
                self.push_back(elt);
                let l = self.len();
                seq_index_mut(&mut self.0, l - 1)
            }
            /// See [`std::collections::LinkedList::push_front`]
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push_front(&mut self, elt: T) {
                let l = seq_len(&self.0);
                let mut right = seq_drain(&mut self.0, 0, l);
                seq_push(&mut self.0, elt);
                seq_concat(&mut self.0, &mut right)
            }
            /// See [`std::collections::LinkedList::push_back`]
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push_back(&mut self, elt: T) {
                seq_push(&mut self.0, elt)
            }
            /// See [`std::collections::LinkedList::pop_front`]
            fn pop_front(&mut self) -> Option<T> {
                if self.len() == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
            /// See [`std::collections::LinkedList::pop_back`]
            fn pop_back(&mut self) -> Option<T> {
                let l = self.len();
                if l == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, l - 1))
                }
            }
            /// See [`std::collections::LinkedList::split_off`]
            #[hax_lib::requires(at <= self.len())]
            fn split_off(&mut self, at: usize) -> LinkedList<T, A>
            where
                A: Clone,
            {
                let l = self.len();
                LinkedList(seq_drain(&mut self.0, at, l), std::marker::PhantomData::<A>)
            }
            /// See [`std::collections::LinkedList::remove`] (unstable in std:
            /// `linked_list_remove`): removes and returns the element at `at`,
            /// panicking when `at` is out of bounds.
            #[hax_lib::requires(at < self.len())]
            fn remove(&mut self, at: usize) -> T {
                seq_remove(&mut self.0, at)
            }
            /// See [`std::collections::LinkedList::contains`].
            ///
            /// Opaque for F* only, for the same reason as
            /// `VecDeque::contains`: hax lowers a generic `PartialEq::eq` to
            /// F*'s primitive `=.`, which demands an `eqtype`.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn contains(&self, x: &T) -> bool
            where
                T: PartialEq<T>,
            {
                let mut found = false;
                for i in 0..self.len() {
                    if seq_index(&self.0, i).eq(x) {
                        found = true
                    }
                }
                found
            }
            /// See [`std::collections::LinkedList::iter`]
            fn iter(&self) -> Iter<'_, T> {
                Iter(seq_from_slice(seq_to_slice(&self.0)))
            }
        }

        impl<'a, T> Iterator for Iter<'a, T> {
            type Item = &'a T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
        }

        #[cfg(test)]
        mod tests {
            use crate::testing::{Inject, panics_like_core};
            use proptest::prelude::*;

            type Model<T> = super::LinkedList<T, crate::alloc::Global>;
            type Std<T> = std::collections::LinkedList<T>;

            impl<T: Clone> Inject for Std<T> {
                type Model = Model<T>;
                fn inject(&self) -> Model<T> {
                    let flat: std::vec::Vec<T> = self.iter().cloned().collect();
                    super::LinkedList(
                        rust_primitives::sequence::seq_from_boxed_slice(flat.into_boxed_slice()),
                        std::marker::PhantomData,
                    )
                }
            }

            fn build(elements: &[u8]) -> (Model<u8>, Std<u8>) {
                let mut std_list = Std::new();
                for &e in elements {
                    std_list.push_back(e);
                }
                (std_list.inject(), std_list)
            }

            proptest! {
                #[test]
                fn test_push_back_len(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let mut model = Model::new();
                    let mut std_list = Std::new();
                    for &e in &elements {
                        model.push_back(e);
                        std_list.push_back(e);
                    }
                    prop_assert_eq!(model.len(), std_list.len());
                    prop_assert_eq!(model, std_list.inject());
                }

                #[test]
                fn test_push_front(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let mut model = Model::new();
                    let mut std_list = Std::new();
                    for &e in &elements {
                        model.push_front(e);
                        std_list.push_front(e);
                    }
                    prop_assert_eq!(model, std_list.inject());
                }

                #[test]
                fn test_len_is_empty(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_list) = build(&elements);
                    prop_assert_eq!(model.len(), std_list.len());
                    prop_assert_eq!(model.is_empty(), std_list.is_empty());
                }

                #[test]
                fn test_pop_front(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model, mut std_list) = build(&elements);
                    for _ in 0..=elements.len() {
                        prop_assert_eq!(model.pop_front(), std_list.pop_front());
                        prop_assert_eq!(&model, &std_list.inject());
                    }
                }

                #[test]
                fn test_pop_back(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model, mut std_list) = build(&elements);
                    for _ in 0..=elements.len() {
                        prop_assert_eq!(model.pop_back(), std_list.pop_back());
                        prop_assert_eq!(&model, &std_list.inject());
                    }
                }

                #[test]
                fn test_front_back(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_list) = build(&elements);
                    prop_assert_eq!(model.front(), std_list.front());
                    prop_assert_eq!(model.back(), std_list.back());
                }

                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_front_back_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                       x in any::<u8>()) {
                    let (mut model, mut std_list) = build(&elements);
                    prop_assert_eq!(model.front_mut().copied(), std_list.front_mut().copied());
                    prop_assert_eq!(model.back_mut().copied(), std_list.back_mut().copied());
                    if let Some(m) = model.front_mut() {
                        *m = x
                    }
                    if let Some(sl) = std_list.front_mut() {
                        *sl = x
                    }
                    prop_assert_eq!(model, std_list.inject());
                }

                // `push_front_mut`/`push_back_mut` are unstable in the std the
                // model crate is built against, so the expectation is pinned: a
                // borrow of the element just pushed.
                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_push_front_back_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                            x in any::<u8>()) {
                    let (mut model, mut std_list) = build(&elements);
                    *model.push_front_mut(x) = x.wrapping_add(1);
                    std_list.push_front(x.wrapping_add(1));
                    *model.push_back_mut(x) = x.wrapping_add(2);
                    std_list.push_back(x.wrapping_add(2));
                    prop_assert_eq!(model, std_list.inject());
                }

                #[test]
                fn test_clear(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model, mut std_list) = build(&elements);
                    model.clear();
                    std_list.clear();
                    prop_assert_eq!(model, std_list.inject());
                }

                #[test]
                fn test_contains(elements in prop::collection::vec(any::<u8>(), 0..20),
                                 x in any::<u8>()) {
                    let (model, std_list) = build(&elements);
                    prop_assert_eq!(model.contains(&x), std_list.contains(&x));
                }

                #[test]
                fn test_append(a in prop::collection::vec(any::<u8>(), 0..20),
                               b in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (mut model_a, mut std_a) = build(&a);
                    let (mut model_b, mut std_b) = build(&b);
                    model_a.append(&mut model_b);
                    std_a.append(&mut std_b);
                    prop_assert_eq!(model_a, std_a.inject());
                    prop_assert_eq!(model_b, std_b.inject());
                }

                #[test]
                fn test_split_off(elements in prop::collection::vec(any::<u8>(), 0..20),
                                  at in 0usize..21) {
                    let (mut model, mut std_list) = build(&elements);
                    let at = at % (std_list.len() + 1);
                    let model_tail = model.split_off(at);
                    let std_tail = std_list.split_off(at);
                    prop_assert_eq!(model, std_list.inject());
                    prop_assert_eq!(model_tail, std_tail.inject());
                }

                // `LinkedList::remove` is unstable in std
                // (`linked_list_remove`), so the expectation is pinned here:
                // it removes and returns the element at `at`.
                #[test]
                fn test_remove(elements in prop::collection::vec(any::<u8>(), 1..20),
                               at in 0usize..20) {
                    let (mut model, std_list) = build(&elements);
                    let at = at % std_list.len();
                    let flat: std::vec::Vec<u8> = std_list.iter().copied().collect();
                    prop_assert_eq!(model.remove(at), flat[at]);
                    let mut expected = flat.clone();
                    expected.remove(at);
                    prop_assert_eq!(
                        rust_primitives::sequence::seq_to_slice(&model.0),
                        &expected[..]
                    );
                }

                #[test]
                fn test_iter(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let (model, std_list) = build(&elements);
                    let from_model: std::vec::Vec<u8> = model.iter().copied().collect();
                    let from_std: std::vec::Vec<u8> = std_list.iter().copied().collect();
                    prop_assert_eq!(from_model, from_std);
                }
            }

            #[test]
            fn test_new() {
                let model = Model::<u8>::new();
                let std_list = Std::<u8>::new();
                assert_eq!(model.len(), std_list.len());
                assert!(model.is_empty());
            }

            // `new_in` is unstable in std (`allocator_api`), so the expectation
            // — an empty list — is pinned here.
            #[test]
            fn test_new_in() {
                let model = Model::<u8>::new_in(crate::alloc::Global);
                assert!(model.is_empty());
            }

            #[test]
            fn test_remove_out_of_bounds_panics() {
                // std's `remove` is unstable, so the reference panic comes from
                // `Vec::remove`, which panics on the same condition.
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.remove(0);
                    },
                    || {
                        let mut v: std::vec::Vec<u8> = std::vec::Vec::new();
                        v.remove(0);
                    },
                );
            }

            #[test]
            fn test_split_off_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.split_off(1);
                    },
                    || {
                        let mut std_list = Std::<u8>::new();
                        std_list.split_off(1);
                    },
                );
            }
        }
    }
    /// Model of `alloc::collections::vec_deque`.
    ///
    /// DEVIATION(std): the deque is backed by one `Seq`, so it is *always
    /// contiguous* — there is no ring buffer and no wrap-around. std leaves
    /// the layout unspecified, so the only observable consequence is that
    /// `as_slices` never splits (see there). Capacity is not modeled at all,
    /// which is why `capacity`/`allocator` are absent.
    ///
    /// The closure-taking methods mirror std's `FnMut` bounds, because Aeneas
    /// passes trait dictionaries positionally and a client call site is typed
    /// from std's signature; their bodies are opaque for F* in exchange, since
    /// hax lowers an `FnMut` call to an arity the F* model of
    /// `FnMut::call_mut` (which takes `&self`) does not have.
    mod vec_deque {
        use hax_lib::ToInt;
        use rust_primitives::sequence::*;
        #[cfg_attr(test, derive(PartialEq, Debug))]
        pub struct VecDeque<T, A>(pub Seq<T>, std::marker::PhantomData<A>);

        // The empty impls keep this module's impl numbering aligned with real
        // `alloc`'s, where `Clone`, `Drop`, `Default` and a private helper
        // block precede the two public inherent blocks. hax derives the F*
        // names `impl_N__method` from that position, so client call sites
        // resolve to `impl_4__new` / `impl_5__push_back` only if the model puts
        // those blocks at index 4 and 5 too.
        //
        // Two things make the count hard to read off std's source, so it is
        // calibrated against what hax actually emits (here and in the other
        // `collections` submodules): hax skips some impl kinds, and it numbers
        // impls carrying a `hax_lib` attribute macro (`attributes`, `opaque`)
        // *after* all the plain ones, keeping their relative order.
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}

        /// Insert `value` at `index`, shifting the tail right. `Seq` has no
        /// element-write primitive, so every positional update in this module
        /// is spelled as this drain/push/concat surgery.
        #[hax_lib::requires(index <= seq_len(s) && seq_len(s) < core::primitive::usize::MAX)]
        fn seq_insert<T>(s: &mut Seq<T>, index: usize, value: T) {
            let l = seq_len(s);
            let mut right = seq_drain(s, index, l);
            seq_push(s, value);
            seq_concat(s, &mut right);
        }

        impl<T> VecDeque<T, crate::alloc::Global> {
            /// See [`std::collections::VecDeque::new`]
            fn new() -> VecDeque<T, crate::alloc::Global> {
                VecDeque(seq_empty(), std::marker::PhantomData)
            }
            /// See [`std::collections::VecDeque::with_capacity`]
            fn with_capacity(_capacity: usize) -> VecDeque<T, crate::alloc::Global> {
                VecDeque::new()
            }
            /// See [`std::collections::VecDeque::try_with_capacity`] (unstable
            /// in std: `try_with_capacity`): the model never fails to
            /// allocate, so this is always `Ok`.
            fn try_with_capacity(
                _capacity: usize,
            ) -> Result<VecDeque<T, crate::alloc::Global>, super::TryReserveError> {
                Ok(VecDeque::new())
            }
        }

        #[hax_lib::attributes]
        impl<T, A> VecDeque<T, A> {
            /// See [`std::collections::VecDeque::new_in`]
            fn new_in(_alloc: A) -> VecDeque<T, A> {
                VecDeque(seq_empty(), std::marker::PhantomData)
            }
            /// See [`std::collections::VecDeque::with_capacity_in`]
            fn with_capacity_in(_capacity: usize, alloc: A) -> VecDeque<T, A> {
                VecDeque::new_in(alloc)
            }
            /// See [`std::collections::VecDeque::len`]
            fn len(&self) -> usize {
                seq_len(&self.0)
            }
            /// See [`std::collections::VecDeque::is_empty`]
            fn is_empty(&self) -> bool {
                seq_len(&self.0) == 0
            }
            /// See [`std::collections::VecDeque::get`]
            fn get(&self, index: usize) -> Option<&T> {
                if index < self.len() {
                    Some(seq_index(&self.0, index))
                } else {
                    None
                }
            }
            /// See [`std::collections::VecDeque::front`]
            fn front(&self) -> Option<&T> {
                self.get(0)
            }
            /// See [`std::collections::VecDeque::back`]
            fn back(&self) -> Option<&T> {
                if self.len() == 0 {
                    None
                } else {
                    self.get(self.len() - 1)
                }
            }
            /// See [`std::collections::VecDeque::get_mut`].
            ///
            /// This and the other `_mut` accessors below are Lean-only: the F*
            /// backend rejects a `&mut` return outright (hax reports "the
            /// mutation of this &mut is not allowed here"), which is the same
            /// reason `core_models::slice::Slice::get_mut` is cfg'd out there.
            #[cfg(not(hax_backend_fstar))]
            fn get_mut(&mut self, index: usize) -> Option<&mut T> {
                if index < self.len() {
                    Some(seq_index_mut(&mut self.0, index))
                } else {
                    None
                }
            }
            /// See [`std::collections::VecDeque::front_mut`]
            #[cfg(not(hax_backend_fstar))]
            fn front_mut(&mut self) -> Option<&mut T> {
                self.get_mut(0)
            }
            /// See [`std::collections::VecDeque::back_mut`]
            #[cfg(not(hax_backend_fstar))]
            fn back_mut(&mut self) -> Option<&mut T> {
                let l = self.len();
                if l == 0 { None } else { self.get_mut(l - 1) }
            }
            /// See [`std::collections::VecDeque::make_contiguous`]: the model's
            /// deque is always contiguous, so this rearranges nothing and just
            /// hands out the whole backing slice.
            #[cfg(not(hax_backend_fstar))]
            fn make_contiguous(&mut self) -> &mut [T] {
                seq_to_slice_mut(&mut self.0)
            }
            /// See [`std::collections::VecDeque::insert_mut`]
            #[cfg(not(hax_backend_fstar))]
            #[hax_lib::requires(index <= self.len() && self.len() < core::primitive::usize::MAX)]
            fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
                seq_insert(&mut self.0, index, value);
                seq_index_mut(&mut self.0, index)
            }
            /// See [`std::collections::VecDeque::push_front_mut`]
            #[cfg(not(hax_backend_fstar))]
            #[hax_lib::requires(seq_len(&self.0) < core::primitive::usize::MAX)]
            fn push_front_mut(&mut self, value: T) -> &mut T {
                self.push_front(value);
                seq_index_mut(&mut self.0, 0)
            }
            /// See [`std::collections::VecDeque::push_back_mut`]
            #[cfg(not(hax_backend_fstar))]
            #[hax_lib::requires(seq_len(&self.0) < core::primitive::usize::MAX)]
            fn push_back_mut(&mut self, value: T) -> &mut T {
                self.push_back(value);
                let l = self.len();
                seq_index_mut(&mut self.0, l - 1)
            }
            // `pop_front_if`/`pop_back_if` are not modeled: their predicate is
            // `FnOnce(&mut T) -> bool`, and the model of `core::ops::FnOnce` has
            // `call_once(&self, args) -> Output`, with no write-back for a `&mut`
            // argument. Aeneas types the call site as returning `(Output × T)`,
            // so Lean rejects a body that binds a plain `bool` ("expected a
            // product type, got Bool"). Same blocker as `retain_mut` and
            // `BTreeMap::retain`; lifting it means changing `core::ops`.
            /// See [`std::collections::VecDeque::push_back`]
            #[hax_lib::requires(seq_len(&self.0) < core::primitive::usize::MAX)]
            fn push_back(&mut self, x: T) {
                seq_push(&mut self.0, x)
            }
            /// See [`std::collections::VecDeque::push_front`]
            #[hax_lib::requires(seq_len(&self.0) < core::primitive::usize::MAX)]
            fn push_front(&mut self, value: T) {
                seq_insert(&mut self.0, 0, value)
            }
            /// See [`std::collections::VecDeque::pop_front`]
            fn pop_front(&mut self) -> Option<T> {
                if self.len() == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
            /// See [`std::collections::VecDeque::pop_back`]
            fn pop_back(&mut self) -> Option<T> {
                let l = self.len();
                if l == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, l - 1))
                }
            }
            /// See [`std::collections::VecDeque::swap`]
            #[hax_lib::requires(i < self.len() && j < self.len())]
            fn swap(&mut self, i: usize, j: usize) {
                if i != j {
                    let lo = if i < j { i } else { j };
                    let hi = if i < j { j } else { i };
                    let high = seq_remove(&mut self.0, hi);
                    let low = seq_remove(&mut self.0, lo);
                    seq_insert(&mut self.0, lo, high);
                    seq_insert(&mut self.0, hi, low)
                }
            }
            /// See [`std::collections::VecDeque::insert`]
            #[hax_lib::requires(index <= self.len() && self.len() < core::primitive::usize::MAX)]
            fn insert(&mut self, index: usize, value: T) {
                seq_insert(&mut self.0, index, value)
            }
            /// See [`std::collections::VecDeque::remove`]
            fn remove(&mut self, index: usize) -> Option<T> {
                if index < self.len() {
                    Some(seq_remove(&mut self.0, index))
                } else {
                    None
                }
            }
            /// See [`std::collections::VecDeque::swap_remove_front`]
            fn swap_remove_front(&mut self, index: usize) -> Option<T> {
                if index < self.len() {
                    self.swap(index, 0);
                    self.pop_front()
                } else {
                    None
                }
            }
            /// See [`std::collections::VecDeque::swap_remove_back`]
            fn swap_remove_back(&mut self, index: usize) -> Option<T> {
                let l = self.len();
                if index < l {
                    self.swap(index, l - 1);
                    self.pop_back()
                } else {
                    None
                }
            }
            /// See [`std::collections::VecDeque::clear`]
            fn clear(&mut self) {
                self.0 = seq_empty()
            }
            /// See [`std::collections::VecDeque::truncate`]
            fn truncate(&mut self, len: usize) {
                let l = self.len();
                if len < l {
                    let _dropped = seq_drain(&mut self.0, len, l);
                }
            }
            /// See [`std::collections::VecDeque::truncate_front`] (unstable in
            /// std: `deque_truncate_front`): keeps the *last* `len` elements.
            fn truncate_front(&mut self, len: usize) {
                let l = self.len();
                if len < l {
                    let _dropped = seq_drain(&mut self.0, 0, l - len);
                }
            }
            /// See [`std::collections::VecDeque::split_off`].
            ///
            /// The `A: Clone` bound is std's, and it has to be mirrored even
            /// though the model never clones the allocator: Aeneas passes a
            /// `Clone A` dictionary as this method's *first* argument, so
            /// dropping the bound makes extracted client code hand the
            /// dictionary in where the receiver belongs.
            #[hax_lib::requires(at <= self.len())]
            fn split_off(&mut self, at: usize) -> VecDeque<T, A>
            where
                A: Clone,
            {
                let l = self.len();
                VecDeque(seq_drain(&mut self.0, at, l), std::marker::PhantomData::<A>)
            }
            /// See [`std::collections::VecDeque::append`]
            #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= core::primitive::usize::MAX.to_int())]
            fn append(&mut self, other: &mut VecDeque<T, A>) {
                seq_concat(&mut self.0, &mut other.0);
                other.0 = seq_empty()
            }
            /// See [`std::collections::VecDeque::rotate_left`]
            #[hax_lib::requires(n <= self.len())]
            fn rotate_left(&mut self, n: usize) {
                let mut head = seq_drain(&mut self.0, 0, n);
                seq_concat(&mut self.0, &mut head)
            }
            /// See [`std::collections::VecDeque::rotate_right`]
            #[hax_lib::requires(n <= self.len())]
            fn rotate_right(&mut self, n: usize) {
                let l = self.len();
                self.rotate_left(l - n)
            }
            /// See [`std::collections::VecDeque::contains`].
            ///
            /// Opaque for F* only: hax lowers a generic `PartialEq::eq` to F*'s
            /// primitive `=.`, which demands an `eqtype`, so the body does not
            /// typecheck at an arbitrary `T` — the same reason
            /// `core_models::slice::Slice::contains` is opaque.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn contains(&self, x: &T) -> bool
            where
                T: PartialEq<T>,
            {
                let mut found = false;
                for i in 0..self.len() {
                    if seq_index(&self.0, i).eq(x) {
                        found = true
                    }
                }
                found
            }
            /// See [`std::collections::VecDeque::as_slices`].
            ///
            /// DEVIATION(std): the model's deque is always contiguous, so the
            /// front slice is the whole deque and the back slice is always
            /// empty. std only promises that the concatenation of the two is
            /// the deque, which is what tests check.
            fn as_slices(&self) -> (&[T], &[T]) {
                let s = seq_to_slice(&self.0);
                (
                    s,
                    rust_primitives::slice::slice_slice(s, self.len(), self.len()),
                )
            }
            /// See [`std::collections::VecDeque::iter`]
            fn iter(&self) -> iter::Iter<'_, T> {
                iter::Iter(seq_from_slice(seq_to_slice(&self.0)))
            }
            /// See [`std::collections::VecDeque::reserve`]: capacity is not
            /// modeled, so this leaves the contents untouched.
            fn reserve(&mut self, _additional: usize) {}
            /// See [`std::collections::VecDeque::reserve_exact`]
            fn reserve_exact(&mut self, _additional: usize) {}
            /// See [`std::collections::VecDeque::shrink_to_fit`]
            fn shrink_to_fit(&mut self) {}
            /// See [`std::collections::VecDeque::shrink_to`]
            fn shrink_to(&mut self, _min_capacity: usize) {}
            /// See [`std::collections::VecDeque::try_reserve`]: the model never
            /// fails to allocate.
            fn try_reserve(&mut self, _additional: usize) -> Result<(), super::TryReserveError> {
                Ok(())
            }
            /// See [`std::collections::VecDeque::try_reserve_exact`]
            fn try_reserve_exact(
                &mut self,
                _additional: usize,
            ) -> Result<(), super::TryReserveError> {
                Ok(())
            }
            /// See [`std::collections::VecDeque::retain`].
            ///
            /// The loop walks indices from the back so that a removal never
            /// shifts an index still to be visited; the invariant is what lets
            /// the backend discharge `seq_remove`'s bound.
            // `FnMut` is std's bound and has to be matched: Aeneas passes
            // trait dictionaries positionally, so changing or dropping it makes
            // extracted client code call this with the dictionary where the
            // receiver belongs. The body is opaque for F* in exchange — hax
            // lowers an `FnMut` call to an arity the F* model of
            // `FnMut::call_mut` (which takes `&self`) does not have.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn retain<F>(&mut self, mut f: F)
            where
                F: FnMut(&T) -> bool,
            {
                let l = self.len();
                for k in 0..l {
                    // Not in the Lean lane: aeneas translates the invariant into `hax_lib`
                    // items the Lean library does not define.
                    #[cfg(not(charon))]
                    hax_lib::loop_invariant!(
                        |k: usize| seq_len(&self.0).to_int() + k.to_int() >= l.to_int()
                    );
                    let i = l - 1 - k;
                    if !f(seq_index(&self.0, i)) {
                        let _removed = seq_remove(&mut self.0, i);
                    }
                }
            }
            /// See [`std::collections::VecDeque::resize_with`]
            // `FnMut` is std's bound and has to be matched: Aeneas passes
            // trait dictionaries positionally, so changing or dropping it makes
            // extracted client code call this with the dictionary where the
            // receiver belongs. The body is opaque for F* in exchange — hax
            // lowers an `FnMut` call to an arity the F* model of
            // `FnMut::call_mut` (which takes `&self`) does not have.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn resize_with<F>(&mut self, new_len: usize, mut generator: F)
            where
                F: FnMut() -> T,
            {
                let l = self.len();
                if new_len > l {
                    for _k in 0..(new_len - l) {
                        seq_push(&mut self.0, generator())
                    }
                } else {
                    self.truncate(new_len)
                }
            }
            /// See [`std::collections::VecDeque::binary_search`].
            ///
            /// DEVIATION(std): a linear scan for the first element that is not
            /// `Less` than `x`, not a bisection. Like std the result is only
            /// meaningful on a sorted deque; std explicitly leaves *which* of
            /// several equal elements is returned unspecified, so returning the
            /// first one is a legal implementation, and it is far easier to
            /// reason about than a bisection.
            fn binary_search(&self, x: &T) -> Result<usize, usize>
            where
                T: Ord,
            {
                self.binary_search_by(|probe| probe.cmp(x))
            }
            /// See [`std::collections::VecDeque::binary_search_by`]. Linear,
            /// for the reason given on `binary_search`.
            // `FnMut` is std's bound and has to be matched: Aeneas passes
            // trait dictionaries positionally, so changing or dropping it makes
            // extracted client code call this with the dictionary where the
            // receiver belongs. The body is opaque for F* in exchange — hax
            // lowers an `FnMut` call to an arity the F* model of
            // `FnMut::call_mut` (which takes `&self`) does not have.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn binary_search_by<F>(&self, mut f: F) -> Result<usize, usize>
            where
                F: FnMut(&T) -> std::cmp::Ordering,
            {
                let mut pos = self.len();
                let mut eq = false;
                let mut done = false;
                for i in 0..self.len() {
                    if !done {
                        match f(seq_index(&self.0, i)) {
                            std::cmp::Ordering::Less => {}
                            std::cmp::Ordering::Equal => {
                                pos = i;
                                eq = true;
                                done = true
                            }
                            std::cmp::Ordering::Greater => {
                                pos = i;
                                eq = false;
                                done = true
                            }
                        }
                    }
                }
                if eq { Ok(pos) } else { Err(pos) }
            }
            /// See [`std::collections::VecDeque::binary_search_by_key`].
            ///
            /// The scan is spelled out rather than delegated to
            /// `binary_search_by`: hax rejects a closure that calls a captured
            /// `FnMut` (hax issue #1060). The `where` clauses are in std's order
            /// (`F` before `B`), which is the order the dictionaries arrive in.
            // `FnMut` is std's bound and has to be matched: Aeneas passes
            // trait dictionaries positionally, so changing or dropping it makes
            // extracted client code call this with the dictionary where the
            // receiver belongs. The body is opaque for F* in exchange — hax
            // lowers an `FnMut` call to an arity the F* model of
            // `FnMut::call_mut` (which takes `&self`) does not have.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn binary_search_by_key<B, F>(&self, b: &B, mut f: F) -> Result<usize, usize>
            where
                F: FnMut(&T) -> B,
                B: Ord,
            {
                let mut pos = self.len();
                let mut eq = false;
                let mut done = false;
                for i in 0..self.len() {
                    if !done {
                        match f(seq_index(&self.0, i)).cmp(b) {
                            std::cmp::Ordering::Less => {}
                            std::cmp::Ordering::Equal => {
                                pos = i;
                                eq = true;
                                done = true
                            }
                            std::cmp::Ordering::Greater => {
                                pos = i;
                                eq = false;
                                done = true
                            }
                        }
                    }
                }
                if eq { Ok(pos) } else { Err(pos) }
            }
            /// See [`std::collections::VecDeque::partition_point`]
            // `FnMut` is std's bound and has to be matched: Aeneas passes
            // trait dictionaries positionally, so changing or dropping it makes
            // extracted client code call this with the dictionary where the
            // receiver belongs. The body is opaque for F* in exchange — hax
            // lowers an `FnMut` call to an arity the F* model of
            // `FnMut::call_mut` (which takes `&self`) does not have.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            fn partition_point<P>(&self, mut pred: P) -> usize
            where
                P: FnMut(&T) -> bool,
            {
                let mut pos = self.len();
                let mut done = false;
                for i in 0..self.len() {
                    if !done && !pred(seq_index(&self.0, i)) {
                        pos = i;
                        done = true
                    }
                }
                pos
            }
        }

        // Real `alloc` puts `resize`/`extend_from_within`/
        // `prepend_from_within` in a `T: Clone` block right after the block
        // above, so this one must stay at impl index 6.
        #[hax_lib::attributes]
        impl<T: Clone, A> VecDeque<T, A> {
            /// See [`std::collections::VecDeque::resize`]
            #[hax_lib::requires(new_len.to_int() < core::primitive::usize::MAX.to_int())]
            fn resize(&mut self, new_len: usize, value: T) {
                let l = self.len();
                if new_len > l {
                    for k in 0..(new_len - l) {
                        // Not in the Lean lane: aeneas translates the invariant into `hax_lib`
                        // items the Lean library does not define.
                        #[cfg(not(charon))]
                        hax_lib::loop_invariant!(
                            |k: usize| seq_len(&self.0).to_int() == l.to_int() + k.to_int()
                        );
                        seq_push(&mut self.0, value.clone())
                    }
                } else {
                    self.truncate(new_len)
                }
            }
        }

        /// Model of `alloc::collections::vec_deque::iter::Iter`, the
        /// shared-borrow iterator returned by
        /// [`std::collections::VecDeque::iter`].
        pub mod iter {
            use rust_primitives::sequence::*;
            pub struct Iter<'a, T>(pub Seq<&'a T>);
            impl<'a, T> Iterator for Iter<'a, T> {
                type Item = &'a T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
        }

        #[hax_lib::attributes]
        impl<T, A> std::ops::Index<usize> for VecDeque<T, A> {
            type Output = T;
            #[hax_lib::requires(i < self.len())]
            fn index(&self, i: usize) -> &T {
                seq_index(&self.0, i)
            }
        }

        pub mod into_iter {
            use rust_primitives::sequence::*;
            pub struct IntoIter<T, A>(pub Seq<T>, pub std::marker::PhantomData<A>);
            impl<T, A> Iterator for IntoIter<T, A> {
                type Item = T;
                fn next(&mut self) -> Option<Self::Item> {
                    if seq_len(&self.0) == 0 {
                        None
                    } else {
                        Some(seq_remove(&mut self.0, 0))
                    }
                }
            }
        }

        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T, A> IntoIterator for VecDeque<T, A> {
            type Item = T;
            type IntoIter = into_iter::IntoIter<T, A>;
            fn into_iter(self) -> Self::IntoIter {
                into_iter::IntoIter(self.0, std::marker::PhantomData)
            }
        }

        // Like `Vec`, `FromIterator` is only implemented for the `Global`
        // allocator (std has no way to thread an allocator through
        // `from_iter`), so `Self` is `VecDeque<T, Global>` — matching the
        // `VecDequeTGlobal` impl name downstream expects.
        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T> std::iter::FromIterator<T> for VecDeque<T, crate::alloc::Global> {
            fn from_iter<I>(iter: I) -> Self
            where
                I: IntoIterator<Item = T>,
            {
                let mut res = VecDeque(seq_empty(), std::marker::PhantomData);
                for el in iter {
                    res.push_back(el)
                }
                res
            }
        }

        #[cfg(hax_backend_fstar)]
        #[hax_lib::fstar::after(
            "
[@@ FStar.Tactics.Typeclasses.tcinstance]
let update_at_usize (#v_T #v_A: Type0)
    : Rust_primitives.Hax.update_at_tc (t_VecDeque v_T v_A) usize =
  {
    super_index = impl_7 #v_T #v_A;
    // `i` is deliberately left unannotated: the class gives it the refinement
    // `f_index_pre self i` (here `i < len self`), and annotating it `usize`
    // would drop exactly the bound `Seq.upd` needs.
    update_at = (fun self i x -> VecDeque (FStar.Seq.upd self._0 (v i) x) self._1)
  }
        "
        )]
        use core::*;

        #[cfg(test)]
        mod tests {
            use crate::testing::{Inject, panics_like_core};
            use proptest::prelude::*;

            type Model<T> = super::VecDeque<T, crate::alloc::Global>;
            type Std<T> = std::collections::VecDeque<T>;

            impl<T: Clone> Inject for Std<T> {
                type Model = Model<T>;
                fn inject(&self) -> Model<T> {
                    let flat: std::vec::Vec<T> = self.iter().cloned().collect();
                    super::VecDeque(
                        rust_primitives::sequence::seq_from_boxed_slice(flat.into_boxed_slice()),
                        std::marker::PhantomData,
                    )
                }
            }

            /// The same `push_back` sequence applied to the model and to std,
            /// so every test below starts from a pair of equal deques. std's
            /// deque is *rotated* by `rot` pops-and-re-pushes first, which is
            /// what makes its internal buffer wrap around; the model is always
            /// contiguous, so this is what checks that the model agrees with a
            /// wrapped std deque.
            fn build(elements: &[u8], rot: usize) -> (Model<u8>, Std<u8>) {
                let mut std_deque = Std::new();
                for &e in elements {
                    std_deque.push_back(e);
                }
                if !elements.is_empty() {
                    for _ in 0..(rot % elements.len().max(1)) {
                        let x = std_deque.pop_front().unwrap();
                        std_deque.push_back(x);
                    }
                }
                (std_deque.inject(), std_deque)
            }

            /// std's `as_slices` may split; the model's never does. Only the
            /// concatenation is a shared observation.
            fn flatten(pair: (&[u8], &[u8])) -> std::vec::Vec<u8> {
                let mut v = pair.0.to_vec();
                v.extend_from_slice(pair.1);
                v
            }

            proptest! {
                #[test]
                fn test_push_back_len_index(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let mut model = Model::new();
                    let mut std_deque = Std::new();
                    for &e in &elements {
                        model.push_back(e);
                        std_deque.push_back(e);
                    }
                    prop_assert_eq!(model.len(), std_deque.len());
                    for i in 0..std_deque.len() {
                        prop_assert_eq!(model[i], std_deque[i]);
                    }
                }

                #[test]
                fn test_into_iter(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let mut model = Model::new();
                    let mut std_deque = std::collections::VecDeque::new();
                    for &e in &elements {
                        model.push_back(e);
                        std_deque.push_back(e);
                    }
                    let mut it = IntoIterator::into_iter(model);
                    let mut collected = std::vec::Vec::new();
                    while let Some(x) = it.next() {
                        collected.push(x);
                    }
                    prop_assert_eq!(collected, std_deque.into_iter().collect::<std::vec::Vec<u8>>());
                }

                #[test]
                fn test_from_iter(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let model: Model<u8> = elements.clone().into_iter().collect();
                    let std_deque: std::collections::VecDeque<u8> =
                        elements.into_iter().collect();
                    prop_assert_eq!(model.len(), std_deque.len());
                    for i in 0..std_deque.len() {
                        prop_assert_eq!(model[i], std_deque[i]);
                    }
                }

                #[test]
                fn test_pop_front(elements in prop::collection::vec(any::<u8>(), 0..20)) {
                    let mut model = Model::with_capacity(elements.len());
                    let mut std_deque = Std::with_capacity(elements.len());
                    for &e in &elements {
                        model.push_back(e);
                        std_deque.push_back(e);
                    }
                    for _ in 0..=elements.len() {
                        prop_assert_eq!(model.pop_front(), std_deque.pop_front());
                    }
                }

                #[test]
                fn test_pop_back(elements in prop::collection::vec(any::<u8>(), 0..20),
                                 rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    for _ in 0..=elements.len() {
                        prop_assert_eq!(model.pop_back(), std_deque.pop_back());
                        prop_assert_eq!(&model, &std_deque.inject());
                    }
                }

                #[test]
                fn test_push_front(elements in prop::collection::vec(any::<u8>(), 0..20),
                                   x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.push_front(x);
                    std_deque.push_front(x);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_len_is_empty(elements in prop::collection::vec(any::<u8>(), 0..20),
                                     rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.len(), std_deque.len());
                    prop_assert_eq!(model.is_empty(), std_deque.is_empty());
                }

                #[test]
                fn test_get(elements in prop::collection::vec(any::<u8>(), 0..20),
                            i in 0usize..25, rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.get(i), std_deque.get(i));
                }

                #[test]
                fn test_front_back(elements in prop::collection::vec(any::<u8>(), 0..20),
                                   rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.front(), std_deque.front());
                    prop_assert_eq!(model.back(), std_deque.back());
                }

                // The `_mut` accessors are only compiled for the non-F* model
                // (the F* backend rejects `&mut` returns), so their tests are
                // too.
                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_get_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                i in 0usize..25, x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    // Same reads, then the same write through the borrow.
                    prop_assert_eq!(model.get_mut(i).copied(), std_deque.get_mut(i).copied());
                    if let Some(m) = model.get_mut(i) {
                        *m = x
                    }
                    if let Some(sd) = std_deque.get_mut(i) {
                        *sd = x
                    }
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_front_back_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                       x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.front_mut().copied(), std_deque.front_mut().copied());
                    prop_assert_eq!(model.back_mut().copied(), std_deque.back_mut().copied());
                    if let Some(m) = model.front_mut() {
                        *m = x
                    }
                    if let Some(sd) = std_deque.front_mut() {
                        *sd = x
                    }
                    if let Some(m) = model.back_mut() {
                        *m = x
                    }
                    if let Some(sd) = std_deque.back_mut() {
                        *sd = x
                    }
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_make_contiguous(elements in prop::collection::vec(any::<u8>(), 0..20),
                                        rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.make_contiguous(), std_deque.make_contiguous());
                    // Writing through the slice must be visible in the deque.
                    if !model.is_empty() {
                        model.make_contiguous()[0] = 42;
                        std_deque.make_contiguous()[0] = 42;
                    }
                    prop_assert_eq!(model, std_deque.inject());
                }

                // `insert_mut`, `push_front_mut` and `push_back_mut` are
                // unstable in the std the model crate is built against, so the
                // expectations are pinned here rather than compared: each
                // returns a borrow of the element it just placed.
                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_insert_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                   i in 0usize..21, x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let i = i % (std_deque.len() + 1);
                    *model.insert_mut(i, x) = x.wrapping_add(1);
                    std_deque.insert(i, x.wrapping_add(1));
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[cfg(not(hax_backend_fstar))]
                #[test]
                fn test_push_front_back_mut(elements in prop::collection::vec(any::<u8>(), 0..20),
                                            x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    *model.push_front_mut(x) = x.wrapping_add(1);
                    std_deque.push_front(x.wrapping_add(1));
                    *model.push_back_mut(x) = x.wrapping_add(2);
                    std_deque.push_back(x.wrapping_add(2));
                    prop_assert_eq!(model, std_deque.inject());
                }


                #[test]
                fn test_swap(elements in prop::collection::vec(any::<u8>(), 1..20),
                             i in 0usize..20, j in 0usize..20, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let (i, j) = (i % std_deque.len(), j % std_deque.len());
                    model.swap(i, j);
                    std_deque.swap(i, j);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_insert(elements in prop::collection::vec(any::<u8>(), 0..20),
                               i in 0usize..21, x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let i = i % (std_deque.len() + 1);
                    model.insert(i, x);
                    std_deque.insert(i, x);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_remove(elements in prop::collection::vec(any::<u8>(), 0..20),
                               i in 0usize..25, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.remove(i), std_deque.remove(i));
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_swap_remove_front(elements in prop::collection::vec(any::<u8>(), 0..20),
                                          i in 0usize..25, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.swap_remove_front(i), std_deque.swap_remove_front(i));
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_swap_remove_back(elements in prop::collection::vec(any::<u8>(), 0..20),
                                         i in 0usize..25, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.swap_remove_back(i), std_deque.swap_remove_back(i));
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_clear(elements in prop::collection::vec(any::<u8>(), 0..20),
                              rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.clear();
                    std_deque.clear();
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_truncate(elements in prop::collection::vec(any::<u8>(), 0..20),
                                 n in 0usize..25, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.truncate(n);
                    std_deque.truncate(n);
                    prop_assert_eq!(model, std_deque.inject());
                }

                // `VecDeque::truncate_front` is unstable in std
                // (`deque_truncate_front`), so the expectation is pinned here:
                // it keeps the last `n` elements.
                #[test]
                fn test_truncate_front(elements in prop::collection::vec(any::<u8>(), 0..20),
                                       n in 0usize..25, rot in 0usize..20) {
                    let (mut model, std_deque) = build(&elements, rot);
                    model.truncate_front(n);
                    let flat: std::vec::Vec<u8> = std_deque.iter().copied().collect();
                    let expected: std::vec::Vec<u8> =
                        flat[flat.len() - n.min(flat.len())..].to_vec();
                    prop_assert_eq!(rust_primitives::sequence::seq_to_slice(&model.0), &expected[..]);
                }

                #[test]
                fn test_split_off(elements in prop::collection::vec(any::<u8>(), 0..20),
                                  at in 0usize..21, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let at = at % (std_deque.len() + 1);
                    let model_tail = model.split_off(at);
                    let std_tail = std_deque.split_off(at);
                    prop_assert_eq!(model, std_deque.inject());
                    prop_assert_eq!(model_tail, std_tail.inject());
                }

                #[test]
                fn test_append(a in prop::collection::vec(any::<u8>(), 0..20),
                               b in prop::collection::vec(any::<u8>(), 0..20),
                               rot in 0usize..20) {
                    let (mut model_a, mut std_a) = build(&a, rot);
                    let (mut model_b, mut std_b) = build(&b, rot);
                    model_a.append(&mut model_b);
                    std_a.append(&mut std_b);
                    prop_assert_eq!(model_a, std_a.inject());
                    prop_assert_eq!(model_b, std_b.inject());
                }

                #[test]
                fn test_rotate_left(elements in prop::collection::vec(any::<u8>(), 0..20),
                                    n in 0usize..21, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let n = n % (std_deque.len() + 1);
                    model.rotate_left(n);
                    std_deque.rotate_left(n);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_rotate_right(elements in prop::collection::vec(any::<u8>(), 0..20),
                                     n in 0usize..21, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    let n = n % (std_deque.len() + 1);
                    model.rotate_right(n);
                    std_deque.rotate_right(n);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_contains(elements in prop::collection::vec(any::<u8>(), 0..20),
                                 x in any::<u8>(), rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    prop_assert_eq!(model.contains(&x), std_deque.contains(&x));
                }

                #[test]
                fn test_as_slices(elements in prop::collection::vec(any::<u8>(), 0..20),
                                  rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    prop_assert_eq!(flatten(model.as_slices()), flatten(std_deque.as_slices()));
                    // The model is always contiguous, unlike std's.
                    prop_assert!(model.as_slices().1.is_empty());
                }

                #[test]
                fn test_iter(elements in prop::collection::vec(any::<u8>(), 0..20),
                             rot in 0usize..20) {
                    let (model, std_deque) = build(&elements, rot);
                    let from_model: std::vec::Vec<u8> = model.iter().copied().collect();
                    let from_std: std::vec::Vec<u8> = std_deque.iter().copied().collect();
                    prop_assert_eq!(from_model, from_std);
                }

                #[test]
                fn test_capacity_ops_preserve_contents(
                    elements in prop::collection::vec(any::<u8>(), 0..20),
                    n in 0usize..40, rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.reserve(n);
                    std_deque.reserve(n);
                    model.reserve_exact(n);
                    std_deque.reserve_exact(n);
                    model.shrink_to(n);
                    std_deque.shrink_to(n);
                    model.shrink_to_fit();
                    std_deque.shrink_to_fit();
                    prop_assert_eq!(model.try_reserve(n), std_deque.try_reserve(n).map_err(|_| unreachable!()));
                    prop_assert_eq!(model.try_reserve_exact(n),
                                    std_deque.try_reserve_exact(n).map_err(|_| unreachable!()));
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_retain(elements in prop::collection::vec(any::<u8>(), 0..20),
                               t in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.retain(|x| *x < t);
                    std_deque.retain(|x| *x < t);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_resize_with(elements in prop::collection::vec(any::<u8>(), 0..20),
                                    n in 0usize..30, x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.resize_with(n, || x);
                    std_deque.resize_with(n, || x);
                    prop_assert_eq!(model, std_deque.inject());
                }

                #[test]
                fn test_resize(elements in prop::collection::vec(any::<u8>(), 0..20),
                               n in 0usize..30, x in any::<u8>(), rot in 0usize..20) {
                    let (mut model, mut std_deque) = build(&elements, rot);
                    model.resize(n, x);
                    std_deque.resize(n, x);
                    prop_assert_eq!(model, std_deque.inject());
                }

                // `binary_search`'s contract is only about sorted input, and
                // std leaves *which* of several equal elements it returns
                // unspecified, so the shared observation is "found or not" plus
                // "the returned index really holds the key".
                #[test]
                fn test_binary_search(elements in prop::collection::vec(any::<u8>(), 0..20),
                                      x in any::<u8>()) {
                    let mut sorted = elements.clone();
                    sorted.sort();
                    let (model, std_deque) = build(&sorted, 0);
                    let m = model.binary_search(&x);
                    let s = std_deque.binary_search(&x);
                    prop_assert_eq!(m.is_ok(), s.is_ok());
                    match (m, s) {
                        (Ok(i), Ok(_)) => prop_assert_eq!(sorted[i], x),
                        (Err(i), Err(j)) => prop_assert_eq!(i, j),
                        _ => unreachable!(),
                    }
                }

                #[test]
                fn test_binary_search_by(elements in prop::collection::vec(any::<u8>(), 0..20),
                                         x in any::<u8>()) {
                    let mut sorted = elements.clone();
                    sorted.sort();
                    let (model, std_deque) = build(&sorted, 0);
                    let m = model.binary_search_by(|p| p.cmp(&x));
                    let s = std_deque.binary_search_by(|p| p.cmp(&x));
                    prop_assert_eq!(m.is_ok(), s.is_ok());
                    if let (Ok(i), Ok(_)) = (m, s) {
                        prop_assert_eq!(sorted[i], x);
                    }
                }

                #[test]
                fn test_binary_search_by_key(pairs in prop::collection::vec((any::<u8>(), any::<u8>()), 0..20),
                                             k in any::<u8>()) {
                    // Keys must be sorted; the payload is the second component.
                    let mut sorted = pairs.clone();
                    sorted.sort_by_key(|p| p.0);
                    let keys: std::vec::Vec<u8> = sorted.iter().map(|p| p.0).collect();
                    let (model, std_deque) = build(&keys, 0);
                    let m = model.binary_search_by_key(&k, |p| *p);
                    let s = std_deque.binary_search_by_key(&k, |p| *p);
                    prop_assert_eq!(m.is_ok(), s.is_ok());
                    if let (Ok(i), Ok(_)) = (m, s) {
                        prop_assert_eq!(keys[i], k);
                    }
                }

                #[test]
                fn test_partition_point(elements in prop::collection::vec(any::<u8>(), 0..20),
                                        x in any::<u8>()) {
                    let mut sorted = elements.clone();
                    sorted.sort();
                    let (model, std_deque) = build(&sorted, 0);
                    prop_assert_eq!(model.partition_point(|p| *p < x),
                                    std_deque.partition_point(|p| *p < x));
                }
            }

            #[test]
            fn test_new() {
                let mut model = Model::<u8>::new();
                let mut std_deque = Std::<u8>::new();
                assert_eq!(model.len(), std_deque.len());
                assert_eq!(model.pop_front(), std_deque.pop_front());
            }

            // `new_in`, `with_capacity_in` and `try_with_capacity` are unstable
            // in std (`allocator_api` / `try_with_capacity`), so the
            // expectation — an empty deque — is pinned here.
            #[test]
            fn test_new_in() {
                let model = Model::<u8>::new_in(crate::alloc::Global);
                assert!(model.is_empty());
                assert_eq!(model.len(), 0);
            }

            #[test]
            fn test_with_capacity_in() {
                let model = Model::<u8>::with_capacity_in(10, crate::alloc::Global);
                assert!(model.is_empty());
            }

            #[test]
            fn test_try_with_capacity() {
                let model = Model::<u8>::try_with_capacity(10);
                assert!(model.is_ok());
                assert!(model.unwrap().is_empty());
            }

            #[test]
            fn test_insert_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.insert(1, 0);
                    },
                    || {
                        let mut std_deque = Std::<u8>::new();
                        std_deque.insert(1, 0);
                    },
                );
            }

            #[test]
            fn test_swap_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.push_back(1);
                        model.swap(0, 1);
                    },
                    || {
                        let mut std_deque = Std::<u8>::new();
                        std_deque.push_back(1);
                        std_deque.swap(0, 1);
                    },
                );
            }

            #[test]
            fn test_split_off_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.split_off(1);
                    },
                    || {
                        let mut std_deque = Std::<u8>::new();
                        std_deque.split_off(1);
                    },
                );
            }

            #[test]
            fn test_rotate_left_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.rotate_left(1);
                    },
                    || {
                        let mut std_deque = Std::<u8>::new();
                        std_deque.rotate_left(1);
                    },
                );
            }

            #[test]
            fn test_rotate_right_out_of_bounds_panics() {
                panics_like_core(
                    || {
                        let mut model = Model::<u8>::new();
                        model.rotate_right(1);
                    },
                    || {
                        let mut std_deque = Std::<u8>::new();
                        std_deque.rotate_right(1);
                    },
                );
            }
        }
    }

    #[cfg(test)]
    mod tests {
        // `TryReserveError`/`TryReserveErrorKind` are only ever constructed by
        // std on allocation failure, and `kind` is unstable
        // (`try_reserve_kind`), so the expectations are pinned here.
        #[test]
        fn test_try_reserve_error_kind() {
            let e = super::TryReserveError(super::TryReserveErrorKind::CapacityOverflow);
            assert_eq!(e.kind(), super::TryReserveErrorKind::CapacityOverflow);
            let e = super::TryReserveError(super::TryReserveErrorKind::AllocError);
            assert_eq!(e.kind(), super::TryReserveErrorKind::AllocError);
        }
    }
}

mod fmt {
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn format(args: core::fmt::Arguments) -> String {
        String::new()
    }

    #[cfg(test)]
    mod tests {
        use proptest::prelude::*;

        proptest! {
            // `fmt::Arguments` is not modelled, so this is a deliberate
            // placeholder (kept opaque for charon; see the Makefile).
            #[test]
            fn test_format_is_a_placeholder(x in any::<u8>()) {
                // Bound first: `prop_assert!` stringifies its argument into a
                // format string, where a literal `{}` would be a placeholder.
                let formatted = super::format(format_args!("{}", x));
                prop_assert!(formatted.is_empty());
            }
        }
    }
}

mod slice {
    // F*-only: `charon::exclude` would drop this dummy type while its `impl`
    // blocks still reference it (see core-models' f32.rs).
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    struct Dummy<T>(T);

    use super::vec::{Vec, from_seq};
    use rust_primitives::sequence::*;

    impl<T> Dummy<T> {
        fn to_vec(s: &[T]) -> Vec<T>
        where
            T: Clone,
        {
            let mut seq = seq_empty();
            seq_extend(&mut seq, s);
            from_seq(seq)
        }
        #[cfg(not(hax_backend_fstar))]
        fn into_vec(s: Box<[T]>) -> Vec<T> {
            from_seq(seq_from_boxed_slice(s))
        }
        #[cfg(hax_backend_fstar)]
        fn into_vec<A>(s: Box<[T]>) -> Vec<T, A> {
            from_seq(seq_from_boxed_slice(s))
        }
        // Mirrors std's `impl<S: Borrow<[T]>, T: Clone> Concat<T> for [S]`.
        #[cfg(not(hax_backend_fstar))]
        fn concat<Item: Clone>(s: &[T]) -> Vec<Item>
        where
            T: core::borrow::Borrow<[Item]>,
        {
            let mut out = seq_empty();
            let mut i = 0;
            while i < rust_primitives::slice::slice_length(s) {
                seq_extend(&mut out, rust_primitives::slice::slice_index(s, i).borrow());
                i += 1;
            }
            from_seq(out)
        }
        // DEVIATION:
        // The F* variant cannot carry the `Borrow` bound: hax erases std's
        // `Concat` bound at call sites, so callers pass `T` and `Item` and no
        // dictionary. Without the bound nothing relates `T` to `[Item]`, so the
        // flattening is not statable and the body is only a placeholder.
        #[cfg(hax_backend_fstar)]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn concat<Item>(s: &[T]) -> Vec<Item> {
            from_seq(seq_empty())
        }
        #[hax_lib::opaque]
        // Insertion sort: charon excludes `sort_by` (see the Makefile), so the
        // body models std for the Rust tests only, over the primitives.
        fn sort_by<F: Fn(&T, &T) -> core::cmp::Ordering>(s: &mut [T], compare: F) {
            use rust_primitives::slice::{slice_index, slice_length, slice_swap};
            let len = slice_length(s);
            let mut i = 1;
            while i < len {
                let mut j = i;
                while j > 0
                    && compare(slice_index(s, j - 1), slice_index(s, j))
                        == core::cmp::Ordering::Greater
                {
                    slice_swap(s, j - 1, j);
                    j -= 1;
                }
                i += 1;
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_to_vec(v in prop::collection::vec(any::<u8>(), 0..100)) {
                let model = super::Dummy::<u8>::to_vec(&v);
                prop_assert_eq!(model.as_slice(), v.as_slice());
            }

            #[test]
            fn test_into_vec(v in prop::collection::vec(any::<u8>(), 0..100)) {
                let boxed: Box<[u8]> = v.clone().into_boxed_slice();
                let model: crate::vec::Vec<u8> = super::Dummy::<u8>::into_vec(boxed);
                prop_assert_eq!(model.as_slice(), v.as_slice());
            }

            #[test]
            fn test_sort_by(v in prop::collection::vec(any::<u8>(), 0..30)) {
                let mut model = v.clone();
                let mut std_slice = v;
                super::Dummy::<u8>::sort_by(&mut model[..], u8::cmp);
                std_slice.sort_by(u8::cmp);
                prop_assert_eq!(model, std_slice);
            }

            // Reverse order exercises the descending comparator as well.
            #[test]
            fn test_sort_by_reversed(v in prop::collection::vec(any::<u8>(), 0..30)) {
                let cmp = |a: &u8, b: &u8| b.cmp(a);
                let mut model = v.clone();
                let mut std_slice = v;
                super::Dummy::<u8>::sort_by(&mut model[..], cmp);
                std_slice.sort_by(cmp);
                prop_assert_eq!(model, std_slice);
            }
        }

        // The F* `concat` is a deliberate placeholder returning an empty `Vec`.
        #[cfg(hax_backend_fstar)]
        proptest! {
            #[test]
            fn test_concat_placeholder_is_empty(v in prop::collection::vec(any::<u8>(), 0..5)) {
                let slices: std::vec::Vec<&[u8]> = v.iter().map(std::slice::from_ref).collect();
                let model: crate::vec::Vec<u8> = super::Dummy::<&[u8]>::concat(&slices);
                prop_assert!(model.as_slice().is_empty());
            }
        }

        // Only the non-F* `concat` is a real model.
        #[cfg(not(hax_backend_fstar))]
        proptest! {
            #[test]
            fn test_concat(vs in prop::collection::vec(
                prop::collection::vec(any::<u8>(), 0..10), 0..10)) {
                let slices: std::vec::Vec<&[u8]> = vs.iter().map(|v| v.as_slice()).collect();
                let model = super::Dummy::<&[u8]>::concat(&slices);
                let expected = slices.concat();
                prop_assert_eq!(model.as_slice(), expected.as_slice());
            }
        }
    }
}

mod string {
    use rust_primitives::sequence::{seq_empty, seq_extend};
    use rust_primitives::string::*;

    /// See [`std::string::ParseError`]: std's deprecated alias for the error of
    /// `String`'s infallible `FromStr` impl.
    pub type ParseError = std::convert::Infallible;

    /// See [`std::string::String`]. The model is a plain string value; there is
    /// no separate buffer, so "capacity" is always exactly the length (see
    /// [`String::capacity`]).
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct String(&'static str);

    /// See [`std::string::FromUtf8Error`]: carries back the bytes that failed
    /// to decode.
    ///
    /// DEVIATION(std): no `utf8_error()`. It returns a `core::str::Utf8Error`,
    /// and the model's `Utf8Error` is a contentless placeholder with no way to
    /// build a value, so the accessor cannot be provided honestly.
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct FromUtf8Error(crate::vec::Vec<u8>);

    // Excluded from F*: hax names *both* inherent impls of this module
    // `impl_String__*`, so `as_bytes`/`into_bytes` here would collide with
    // `String`'s. The type itself still extracts, so `from_utf8`'s signature is
    // unaffected.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    impl FromUtf8Error {
        /// See [`std::string::FromUtf8Error::as_bytes`]
        fn as_bytes(&self) -> &[u8] {
            self.0.as_slice()
        }
        /// See [`std::string::FromUtf8Error::into_bytes`]
        fn into_bytes(self) -> crate::vec::Vec<u8> {
            self.0
        }
        /// See `std::string::FromUtf8Error::into_utf8_lossy` (unstable).
        fn into_utf8_lossy(self) -> String {
            String(str_from_utf8_lossy(self.0.as_slice()))
        }
    }

    /// See [`std::string::ToString`].
    ///
    /// In real core `to_string` is a required method of `ToString` and the
    /// trait is blanket-implemented over `Display`; the model mirrors both.
    pub trait ToString {
        /// See [`std::string::ToString::to_string`]
        fn to_string(&self) -> String;
    }

    // Opaque: running a `Display` implementation is not expressible in the
    // model, so the body below is a Rust-side oracle only.
    #[hax_lib::opaque]
    impl<T: std::fmt::Display> ToString for T {
        fn to_string(&self) -> String {
            String(str_of_display(self))
        }
    }

    #[hax_lib::attributes]
    impl String {
        /// See [`std::string::String::new`]
        fn new() -> Self {
            String("")
        }
        /// See [`std::string::String::with_capacity`]: the requested capacity
        /// is irrelevant to the model (see [`String::capacity`]).
        fn with_capacity(_capacity: usize) -> Self {
            String("")
        }
        /// See `std::string::String::try_with_capacity` (unstable). The model
        /// never fails to allocate.
        fn try_with_capacity(
            _capacity: usize,
        ) -> Result<Self, crate::collections::TryReserveError> {
            Ok(String(""))
        }
        /// See [`std::string::String::from_utf8`]
        fn from_utf8(vec: crate::vec::Vec<u8>) -> Result<Self, FromUtf8Error> {
            if str_is_utf8(vec.as_slice()) {
                Ok(String(str_from_utf8_lossy(vec.as_slice())))
            } else {
                Err(FromUtf8Error(vec))
            }
        }
        /// See [`std::string::String::from_utf8_lossy`].
        ///
        /// DEVIATION(std): returns a `String` rather than a `Cow<'_, str>`. The
        /// model's `Cow<T>` is sized-only, so `Cow<'_, str>` is not statable.
        fn from_utf8_lossy(v: &[u8]) -> Self {
            String(str_from_utf8_lossy(v))
        }
        /// See `std::string::String::from_utf8_lossy_owned` (unstable).
        fn from_utf8_lossy_owned(v: crate::vec::Vec<u8>) -> Self {
            String(str_from_utf8_lossy(v.as_slice()))
        }
        /// See [`std::string::String::push_str`]
        fn push_str(&mut self, other: &'static str) {
            *self = String(str_concat(self.0, other))
        }
        /// See [`std::string::String::push`]
        fn push(&mut self, c: char) {
            *self = String(str_concat(self.0, str_of_char(c)))
        }
        /// See [`std::string::String::pop`]
        fn pop(&mut self) -> Option<char> {
            // Char count, not `str::len`: the primitives below index by char.
            let l = str_len(self.0);
            if l > 0 {
                let c = str_index(self.0, l - 1);
                *self = String(str_sub(self.0, 0, l - 1));
            // `str_index`/`str_sub` count chars, so the length has to as well —
            // `self.0.len()` is bytes. Read the last char before truncating:
            // afterwards `n - 1` is out of bounds.
            let n = str_char_count(self.0);
            if n > 0 {
                let c = str_index(self.0, n - 1);
                *self = String(str_sub(self.0, 0, n - 1));
                Some(c)
            } else {
                None
            }
        }
        /// See [`std::string::String::len`]: the length in **bytes**.
        fn len(&self) -> usize {
            self.0.len()
        }
        /// See [`std::string::String::is_empty`]
        fn is_empty(&self) -> bool {
            self.0.len() == 0
        }
        /// See [`std::string::String::as_str`]
        fn as_str(&self) -> &str {
            self.0
        }
        /// See [`std::string::String::as_bytes`]
        fn as_bytes(&self) -> &[u8] {
            self.0.as_bytes()
        }
        /// See [`std::string::String::into_bytes`]
        fn into_bytes(self) -> crate::vec::Vec<u8> {
            let mut seq = seq_empty();
            seq_extend(&mut seq, self.0.as_bytes());
            crate::vec::from_seq(seq)
        }
        /// See [`std::string::String::into_boxed_str`]
        fn into_boxed_str(self) -> Box<str> {
            Box::from(self.0)
        }
        /// See [`std::string::String::clear`]
        fn clear(&mut self) {
            *self = String("")
        }
        /// See [`std::string::String::truncate`]: `new_len` is a **byte**
        /// index, and a `new_len` past the end is a no-op rather than a panic.
        #[hax_lib::requires(new_len > self.0.len() || str_is_char_boundary(self.0, new_len))]
        fn truncate(&mut self, new_len: usize) {
            if new_len <= self.0.len() {
                *self = String(str_sub_bytes(self.0, 0, new_len))
            }
        }
        /// See [`std::string::String::split_off`]: `at` is a **byte** index.
        #[hax_lib::requires(str_is_char_boundary(self.0, at))]
        fn split_off(&mut self, at: usize) -> String {
            let l = self.0.len();
            let tail = String(str_sub_bytes(self.0, at, l));
            *self = String(str_sub_bytes(self.0, 0, at));
            tail
        }
        /// See [`std::string::String::insert_str`]: `idx` is a **byte** index.
        #[hax_lib::requires(str_is_char_boundary(self.0, idx))]
        fn insert_str(&mut self, idx: usize, string: &'static str) {
            let l = self.0.len();
            *self = String(str_concat(
                str_concat(str_sub_bytes(self.0, 0, idx), string),
                str_sub_bytes(self.0, idx, l),
            ))
        }
        /// See [`std::string::String::insert`]: `idx` is a **byte** index, `ch`
        /// is inserted in its UTF-8 encoding.
        #[hax_lib::requires(str_is_char_boundary(self.0, idx))]
        fn insert(&mut self, idx: usize, ch: char) {
            self.insert_str(idx, str_of_char(ch))
        }
        /// See [`std::string::String::remove`]: `idx` is the **byte** index of
        /// the char to remove.
        #[hax_lib::requires(idx < self.0.len() && str_is_char_boundary(self.0, idx))]
        fn remove(&mut self, idx: usize) -> char {
            let l = self.0.len();
            // The tail is spelled as "drop the first char of `self[idx..]`"
            // rather than "`self[idx + ch.len_utf8()..]`" so that no arithmetic
            // on byte offsets appears in the extraction.
            let tail = str_sub_bytes(self.0, idx, l);
            let ch = str_index(tail, 0);
            *self = String(str_concat(
                str_sub_bytes(self.0, 0, idx),
                str_sub(tail, 1, str_char_count(tail)),
            ));
            ch
        }
        /// See [`std::string::String::retain`].
        ///
        /// Opaque: the body below is the real filter, and `cargo test` checks it
        /// against std, but it does not survive extraction — the model's `Fn*`
        /// traits carry `Output` as a non-method field, so F* cannot see that
        /// `f(c)` is a `bool` and rejects the `if`.
        #[hax_lib::opaque]
        fn retain<F>(&mut self, mut f: F)
        where
            F: FnMut(char) -> bool,
        {
            let n = str_char_count(self.0);
            let mut kept = "";
            for i in 0..n {
                let c = str_index(self.0, i);
                if f(c) {
                    kept = str_concat(kept, str_of_char(c));
                }
            }
            *self = String(kept)
        }
        /// See [`std::string::String::capacity`].
        ///
        /// DEVIATION(std): the model holds a string value, not a buffer, so the
        /// capacity is always exactly the length. std only guarantees
        /// `capacity() >= len()`, which this respects, but the concrete numbers
        /// it reports differ.
        fn capacity(&self) -> usize {
            self.0.len()
        }
        /// See [`std::string::String::reserve`]: a no-op, as the model has no
        /// buffer to grow.
        fn reserve(&mut self, _additional: usize) {}
        /// See [`std::string::String::reserve_exact`]: a no-op, as
        /// [`String::reserve`].
        fn reserve_exact(&mut self, _additional: usize) {}
        /// See [`std::string::String::try_reserve`]: the model never fails to
        /// allocate.
        fn try_reserve(
            &mut self,
            _additional: usize,
        ) -> Result<(), crate::collections::TryReserveError> {
            Ok(())
        }
        /// See [`std::string::String::try_reserve_exact`]: as
        /// [`String::try_reserve`].
        fn try_reserve_exact(
            &mut self,
            _additional: usize,
        ) -> Result<(), crate::collections::TryReserveError> {
            Ok(())
        }
        /// See [`std::string::String::shrink_to_fit`]: a no-op, as
        /// [`String::reserve`].
        fn shrink_to_fit(&mut self) {}
        /// See [`std::string::String::shrink_to`]: a no-op, as
        /// [`String::reserve`].
        fn shrink_to(&mut self, _min_capacity: usize) {}
    }

    #[cfg(test)]
    mod tests {
        use crate::testing::Inject;
        use proptest::prelude::*;

        /// Mixes 1-, 2- and 3-byte chars so that the byte/char index
        /// distinction is actually exercised.
        const STR: &str = "[a-cé☃]{0,10}";

        impl Inject for std::string::String {
            type Model = super::String;
            fn inject(&self) -> super::String {
                // Built with `push` (itself tested below) rather than by
                // wrapping the `&str`, which would need a `'static` lifetime.
                let mut model = super::String::new();
                for c in self.chars() {
                    model.push(c);
                }
                model
            }
        }

        /// Proptest hands out owned `String`s, but the model's `&str`-taking
        /// methods want `&'static str`. Leaking is fine at test scale.
        fn leak(s: &str) -> &'static str {
            Box::leak(s.to_string().into_boxed_str())
        }

        /// A char boundary of `s` picked by `k`: the start of one of its chars,
        /// or `s.len()`. Drawing byte indices uniformly instead rejects almost
        /// everything, since most of `0..40` is out of range.
        fn boundary(s: &str, k: usize) -> usize {
            let mut offsets: std::vec::Vec<usize> = s.char_indices().map(|(i, _)| i).collect();
            offsets.push(s.len());
            offsets[k % offsets.len()]
        }

        /// As [`boundary`], but never `s.len()`: the start of a char of a
        /// non-empty `s`.
        fn char_start(s: &str, k: usize) -> usize {
            let offsets: std::vec::Vec<usize> = s.char_indices().map(|(i, _)| i).collect();
            offsets[k % offsets.len()]
        }

        proptest! {
            #[test]
            fn test_push(s in STR, c in any::<char>()) {
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.push(c);
                std_s.push(c);
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_push_str(s in STR, other in STR) {
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.push_str(leak(&other));
                std_s.push_str(&other);
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_pop(s in STR) {
                let mut model = s.inject();
                let mut std_s = s.clone();
                prop_assert_eq!(model.pop(), std_s.pop());
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_len(s in STR) {
                prop_assert_eq!(s.inject().len(), s.len());
            }

            #[test]
            fn test_is_empty(s in STR) {
                prop_assert_eq!(s.inject().is_empty(), s.is_empty());
            }

            #[test]
            fn test_as_str(s in STR) {
                let model = s.inject();
                prop_assert_eq!(model.as_str(), s.as_str());
            }

            #[test]
            fn test_as_bytes(s in STR) {
                let model = s.inject();
                prop_assert_eq!(model.as_bytes(), s.as_bytes());
            }

            #[test]
            fn test_into_bytes(s in STR) {
                let model = s.inject().into_bytes();
                let std_bytes = s.clone().into_bytes();
                prop_assert_eq!(model.as_slice(), std_bytes.as_slice());
            }

            #[test]
            fn test_into_boxed_str(s in STR) {
                prop_assert_eq!(s.inject().into_boxed_str(), s.clone().into_boxed_str());
            }

            #[test]
            fn test_clear(s in STR) {
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.clear();
                std_s.clear();
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_truncate(s in STR, new_len in 0usize..40) {
                prop_assume!(new_len > s.len() || s.is_char_boundary(new_len));
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.truncate(new_len);
                std_s.truncate(new_len);
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_split_off(s in STR, k in 0usize..16) {
                let at = boundary(&s, k);
                let mut model = s.inject();
                let mut std_s = s.clone();
                let model_tail = model.split_off(at);
                let std_tail = std_s.split_off(at);
                prop_assert_eq!(model, std_s.inject());
                prop_assert_eq!(model_tail, std_tail.inject());
            }

            #[test]
            fn test_insert_str(s in STR, other in STR, k in 0usize..16) {
                let idx = boundary(&s, k);
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.insert_str(idx, leak(&other));
                std_s.insert_str(idx, &other);
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_insert(s in STR, c in any::<char>(), k in 0usize..16) {
                let idx = boundary(&s, k);
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.insert(idx, c);
                std_s.insert(idx, c);
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_remove(s in STR, k in 0usize..16) {
                prop_assume!(!s.is_empty());
                let idx = char_start(&s, k);
                let mut model = s.inject();
                let mut std_s = s.clone();
                prop_assert_eq!(model.remove(idx), std_s.remove(idx));
                prop_assert_eq!(model, std_s.inject());
            }

            #[test]
            fn test_retain(s in STR) {
                let mut model = s.inject();
                let mut std_s = s.clone();
                model.retain(|c| c != 'a');
                std_s.retain(|c| c != 'a');
                prop_assert_eq!(model, std_s.inject());
            }

            /// std only promises `capacity() >= len()`; the model reports
            /// exactly `len()` (see `String::capacity`), so that inequality and
            /// the preservation of the contents are all there is to check —
            /// here across every capacity-shaped method.
            #[test]
            fn test_capacity_ops(s in STR, n in 0usize..40) {
                let mut model = s.inject();
                model.reserve(n);
                prop_assert!(model.capacity() >= model.len());
                model.reserve_exact(n);
                prop_assert!(model.try_reserve(n).is_ok());
                prop_assert!(model.try_reserve_exact(n).is_ok());
                model.shrink_to(n);
                model.shrink_to_fit();
                prop_assert!(model.capacity() >= model.len());
                prop_assert_eq!(model, s.inject());
            }

            #[test]
            fn test_from_utf8_valid(s in STR) {
                let model = super::String::from_utf8(s.clone().into_bytes().inject());
                prop_assert_eq!(model, Ok(s.inject()));
            }

            #[test]
            fn test_from_utf8_lossy(bytes in prop::collection::vec(any::<u8>(), 0..20)) {
                let model = super::String::from_utf8_lossy(&bytes);
                prop_assert_eq!(model, std::string::String::from_utf8_lossy(&bytes).into_owned().inject());
            }

            #[test]
            fn test_from_utf8_lossy_owned(bytes in prop::collection::vec(any::<u8>(), 0..20)) {
                let model = super::String::from_utf8_lossy_owned(bytes.inject());
                prop_assert_eq!(model, std::string::String::from_utf8_lossy(&bytes).into_owned().inject());
            }

            #[test]
            fn test_from_utf8_error(bytes in prop::collection::vec(any::<u8>(), 0..20)) {
                let std_err = match std::string::String::from_utf8(bytes.clone()) {
                    Ok(_) => return Ok(()),
                    Err(e) => e,
                };
                let err = match super::String::from_utf8(bytes.inject()) {
                    Ok(_) => panic!("the model accepted invalid UTF-8"),
                    Err(e) => e,
                };
                prop_assert_eq!(err.as_bytes(), std_err.as_bytes());
                prop_assert_eq!(
                    err.into_utf8_lossy(),
                    std::string::String::from_utf8_lossy(&bytes).into_owned().inject()
                );
                let err = super::String::from_utf8(bytes.inject()).unwrap_err();
                let model_bytes = err.into_bytes();
                let std_bytes = std_err.into_bytes();
                prop_assert_eq!(model_bytes.as_slice(), std_bytes.as_slice());
            }

            #[test]
            fn test_to_string(n in any::<u32>()) {
                prop_assert_eq!(super::ToString::to_string(&n), n.to_string().inject());
            }
        }

        #[test]
        fn test_new() {
            let model = super::String::new();
            assert_eq!(model, std::string::String::new().inject());
        }

        #[test]
        fn test_with_capacity() {
            let model = super::String::with_capacity(10);
            assert_eq!(model, std::string::String::with_capacity(10).inject());
        }

        #[test]
        fn test_try_with_capacity() {
            let model = super::String::try_with_capacity(10);
            assert!(model.is_ok());
            assert_eq!(model.unwrap(), std::string::String::new().inject());
        }

        // ----- panics ---------------------------------------------------------

        #[test]
        fn test_truncate_non_boundary_panics() {
            let mut model = "aé".to_string().inject();
            let mut real = "aé".to_string();
            let i = std::hint::black_box(2usize);
            crate::testing::panics_like_core(|| model.truncate(i), || real.truncate(i));
        }

        #[test]
        fn test_split_off_past_end_panics() {
            let mut model = "abc".to_string().inject();
            let mut real = "abc".to_string();
            let at = std::hint::black_box(4usize);
            crate::testing::panics_like_core(|| model.split_off(at), || real.split_off(at));
        }

        #[test]
        fn test_insert_past_end_panics() {
            let mut model = "abc".to_string().inject();
            let mut real = "abc".to_string();
            let i = std::hint::black_box(4usize);
            crate::testing::panics_like_core(|| model.insert(i, 'x'), || real.insert(i, 'x'));
        }

        #[test]
        fn test_insert_str_non_boundary_panics() {
            let mut model = "aé".to_string().inject();
            let mut real = "aé".to_string();
            let i = std::hint::black_box(2usize);
            crate::testing::panics_like_core(
                || model.insert_str(i, "x"),
                || real.insert_str(i, "x"),
            );
        }

        #[test]
        fn test_remove_past_end_panics() {
            let mut model = "abc".to_string().inject();
            let mut real = "abc".to_string();
            let i = std::hint::black_box(3usize);
            crate::testing::panics_like_core(|| model.remove(i), || real.remove(i));
        }

        #[test]
        fn test_remove_non_boundary_panics() {
            let mut model = "aé".to_string().inject();
            let mut real = "aé".to_string();
            let i = std::hint::black_box(2usize);
            crate::testing::panics_like_core(|| model.remove(i), || real.remove(i));
        }

        proptest! {
            // Arbitrary chars, including multi-byte ones: indexing by char
            // where `str::len` counts bytes is exactly the bug this catches.
            #[test]
            fn test_pop(cs in prop::collection::vec(any::<char>(), 0..8)) {
                let mut model = super::String::new();
                let mut std_s = std::string::String::new();
                for c in &cs {
                    model.push(*c);
                    std_s.push(*c);
                }
                prop_assert_eq!(model.pop(), std_s.pop());
                prop_assert_eq!(model.0, std_s);
            }
        }
    }
}

#[cfg(not(hax_backend_fstar))]
pub mod vec {
    // TODO drain (to be done with iterators)
    use hax_lib::ToInt;
    use rust_primitives::sequence::*;

    #[cfg_attr(test, derive(Debug))]
    #[hax_lib::fstar::before("open Rust_primitives.Notations")]
    pub struct Vec<T>(pub Seq<T>);

    /// Build a `Vec` from a raw sequence. Used by the `collections` and
    /// `slice` modules so their constructor sites stay identical across the
    /// two `vec` variants (the F* variant threads `A` through here).
    pub(crate) fn from_seq<T>(s: Seq<T>) -> Vec<T> {
        Vec(s)
    }

    impl<T: Clone> Clone for Vec<T> {
        fn clone(&self) -> Self {
            let mut new_vec = seq_empty();
            for it in self.iter() {
                seq_push(&mut new_vec, it.clone());
            }
            Vec(new_vec)
        }
    }
    impl<T, U> PartialEq<Vec<U>> for Vec<T>
    where
        T: PartialEq<U>,
    {
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &Vec<U>) -> bool {
            self.eq(other) == false
        }
        fn eq(&self, other: &Vec<U>) -> bool {
            if !(self.len() == other.len()) {
                false
            } else {
                let mut res = true;
                for i in 0..self.len() {
                    // `res &&` keeps this short-circuiting like std's early
                    // return: once unequal, `T::eq` is not called again (it may
                    // panic). Aeneas has no early return, hence the flag.
                    if res && !(self[i] == other[i]) {
                        res = false
                    }
                }
                res
            }
        }
    }

    /// Opaque model of `std::vec::IntoIter<T, A>`. Downstream Aeneas
    /// extractions reference this type via its full path
    /// `alloc::vec::into_iter::IntoIter<T, A>`, so we expose it under a
    /// matching submodule.
    pub mod into_iter {
        use rust_primitives::sequence::*;
        pub struct IntoIter<T>(pub Seq<T>);
        impl<T> Iterator for IntoIter<T> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
        }
        impl<T> IntoIter<T> {
            /// See [`std::vec::IntoIter::as_slice`]: the elements not yet
            /// yielded.
            pub fn as_slice(&self) -> &[T] {
                seq_to_slice(&self.0)
            }
            /// See [`std::vec::IntoIter::as_mut_slice`]
            pub fn as_mut_slice(&mut self) -> &mut [T] {
                seq_to_slice_mut(&mut self.0)
            }
            /// See [`std::vec::IntoIter::allocator`]: see `Drain::allocator`.
            pub fn allocator(&self) -> crate::alloc::Global {
                crate::alloc::Global
            }
        }
    }

    impl<T> IntoIterator for Vec<T> {
        type Item = T;
        type IntoIter = into_iter::IntoIter<T>;
        fn into_iter(self) -> Self::IntoIter {
            into_iter::IntoIter(self.0)
        }
    }

    fn from_elem<T: Clone>(item: T, len: usize) -> Vec<T> {
        Vec(seq_create(item, len))
    }

    #[hax_lib::attributes]
    impl<T> Vec<T> {
        pub fn new() -> Vec<T> {
            Vec(seq_empty())
        }
        pub fn with_capacity(_c: usize) -> Vec<T> {
            Vec::new()
        }
    }

    /// See [`std::vec::Vec::default`]: an empty `Vec`.
    impl<T> Default for Vec<T> {
        fn default() -> Vec<T> {
            Vec::new()
        }
    }

    #[hax_lib::attributes]
    impl<T> Vec<T> {
        pub fn len(&self) -> usize {
            seq_len(&self.0)
        }
        #[hax_lib::requires(seq_len(&self.0) < usize::MAX)]
        pub fn push(&mut self, x: T) {
            seq_push(&mut self.0, x)
        }
        pub fn pop(&mut self) -> Option<T> {
            let l = seq_len(&self.0);
            if l > 0 {
                let last = seq_remove(&mut self.0, l - 1);
                Some(last)
            } else {
                None
            }
        }
        pub fn is_empty(&self) -> bool {
            seq_len(&self.0) == 0
        }
        #[hax_lib::requires(index <= seq_len(&self.0) && seq_len(&self.0) < usize::MAX)]
        pub fn insert(&mut self, index: usize, element: T) {
            let l = seq_len(&self.0);
            let mut right = seq_drain(&mut self.0, index, l);
            seq_push(&mut self.0, element);
            seq_concat(&mut self.0, &mut right);
        }
        pub fn as_slice(&self) -> &[T] {
            seq_to_slice(&self.0)
        }
        // These are opaque for F* only: a bare `#[hax_lib::opaque]` is invisible to
        // charon, so aeneas extracts the body regardless and it must model std.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn truncate(&mut self, n: usize) {
            let l = seq_len(&self.0);
            if n < l {
                seq_drain(&mut self.0, n, l);
            }
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::requires(n < self.len())]
        pub fn swap_remove(&mut self, n: usize) -> T {
            let l = seq_len(&self.0);
            let last = seq_remove(&mut self.0, l - 1);
            if n == l - 1 {
                last
            } else {
                let removed = seq_remove(&mut self.0, n);
                self.insert(n, last);
                removed
            }
        }
        /// `remove` drops one element, so it never grows the vector. The exact
        /// `len' = len - 1` would need `index < len` as a precondition (else on
        /// an empty vector it asserts a `usize` is `-1`), which callers holding
        /// only a length upper bound cannot discharge, so state the inequality.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::ensures(|_| future(self).len().to_int() <= self.len().to_int())]
        pub fn remove(&mut self, index: usize) -> T {
            seq_remove(&mut self.0, index)
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn clear(&mut self) {
            self.0 = seq_empty()
        }
        #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= usize::MAX.to_int())]
        pub fn append(&mut self, other: &mut Vec<T>) {
            seq_concat(&mut self.0, &mut other.0);
            other.0 = seq_empty()
        }
        /// See [`std::vec::Vec::split_off`]: truncate `self` to `[0, at)` and
        /// return the tail `[at, len)` as a new `Vec`.
        #[hax_lib::requires(at <= self.len())]
        pub fn split_off(&mut self, at: usize) -> Vec<T> {
            let l = seq_len(&self.0);
            Vec(seq_drain(&mut self.0, at, l))
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn drain<R /* : RangeBounds<usize> */>(
            &mut self,
            _range: R,
        ) -> drain::Drain<T, crate::alloc::Global> {
            let l = seq_len(&self.0);
            drain::Drain(
                seq_drain(&mut self.0, 0, l),
                std::marker::PhantomData::<crate::alloc::Global>,
            ) // TODO use range bounds
        }
        /// See [`std::vec::Vec::capacity`].
        //
        // DEVIATION(std): the model's `Vec` is a `Seq`, which has no capacity
        // distinct from its length — `with_capacity` already forgets its
        // argument — so the model's capacity is *exact*. std's weaker guarantee
        // `capacity() >= len()` still holds, but
        // `Vec::with_capacity(n).capacity() >= n` does not.
        pub fn capacity(&self) -> usize {
            seq_len(&self.0)
        }
        /// See [`std::vec::Vec::reserve`]: a no-op, the model's `Vec` never
        /// reallocates. (The same goes for the four methods below.)
        pub fn reserve(&mut self, _additional: usize) {}
        /// See [`std::vec::Vec::reserve_exact`]
        pub fn reserve_exact(&mut self, _additional: usize) {}
        /// See [`std::vec::Vec::shrink_to_fit`]
        pub fn shrink_to_fit(&mut self) {}
        /// See [`std::vec::Vec::shrink_to`]
        pub fn shrink_to(&mut self, _min_capacity: usize) {}
        /// See [`std::vec::Vec::try_reserve`]: always succeeds, see `reserve`.
        pub fn try_reserve(
            &mut self,
            _additional: usize,
        ) -> Result<(), crate::collections::TryReserveError> {
            Ok(())
        }
        /// See [`std::vec::Vec::try_reserve_exact`]
        pub fn try_reserve_exact(
            &mut self,
            _additional: usize,
        ) -> Result<(), crate::collections::TryReserveError> {
            Ok(())
        }
        /// See [`std::vec::Vec::try_with_capacity`]
        pub fn try_with_capacity(
            _capacity: usize,
        ) -> Result<Vec<T>, crate::collections::TryReserveError> {
            Ok(Vec::new())
        }
        /// See [`std::vec::Vec::new_in`].
        //
        // DEVIATION(std): this `Vec` carries no allocator parameter, so the
        // allocator argument is dropped. Same for the two methods below. `A` is
        // deliberately unbounded: Aeneas's name map for `Vec` drops the
        // allocator, so a client's call site passes no `Allocator` dictionary
        // and an `A: Allocator` bound here would be an arity mismatch.
        pub fn new_in<A>(_alloc: A) -> Vec<T> {
            Vec::new()
        }
        /// See [`std::vec::Vec::with_capacity_in`]
        pub fn with_capacity_in<A>(_c: usize, _alloc: A) -> Vec<T> {
            Vec::new()
        }
        /// See [`std::vec::Vec::try_with_capacity_in`]
        pub fn try_with_capacity_in<A>(
            _c: usize,
            _alloc: A,
        ) -> Result<Vec<T>, crate::collections::TryReserveError> {
            Ok(Vec::new())
        }
        /// See [`std::vec::Vec::allocator`]: this `Vec` has no allocator
        /// parameter, it is always global-allocated.
        //
        // DEVIATION(std): returns the allocator by value rather than by
        // reference. `&Global` is a promoted constant, which Aeneas cannot
        // translate; extraction erases shared borrows anyway, so the two agree
        // in the backends.
        pub fn allocator(&self) -> crate::alloc::Global {
            crate::alloc::Global
        }
        /// See [`std::vec::Vec::as_mut_slice`]
        pub fn as_mut_slice(&mut self) -> &mut [T] {
            seq_to_slice_mut(&mut self.0)
        }
        /// See [`std::vec::Vec::into_boxed_slice`]
        pub fn into_boxed_slice(self) -> Box<[T]> {
            seq_into_boxed_slice(self.0)
        }
        /// See [`std::vec::Vec::try_remove`]
        pub fn try_remove(&mut self, index: usize) -> Option<T> {
            if index < seq_len(&self.0) {
                Option::Some(seq_remove(&mut self.0, index))
            } else {
                Option::None
            }
        }
        /// See [`std::vec::Vec::insert_mut`]
        #[hax_lib::requires(index <= seq_len(&self.0) && seq_len(&self.0) < usize::MAX)]
        pub fn insert_mut(&mut self, index: usize, element: T) -> &mut T {
            self.insert(index, element);
            seq_index_mut(&mut self.0, index)
        }
        /// See [`std::vec::Vec::push_mut`]
        #[hax_lib::requires(seq_len(&self.0) < usize::MAX)]
        pub fn push_mut(&mut self, value: T) -> &mut T {
            seq_push(&mut self.0, value);
            let l = seq_len(&self.0);
            seq_index_mut(&mut self.0, l - 1)
        }
        /// See [`std::vec::Vec::pop_if`]
        pub fn pop_if<F: Fn(&T) -> bool>(&mut self, predicate: F) -> Option<T> {
            let l = seq_len(&self.0);
            if l == 0 {
                Option::None
            } else if predicate(seq_index(&self.0, l - 1)) {
                Option::Some(seq_remove(&mut self.0, l - 1))
            } else {
                Option::None
            }
        }
        /// See [`std::vec::Vec::resize_with`]
        pub fn resize_with<F: Fn() -> T>(&mut self, new_len: usize, f: F) {
            let l = seq_len(&self.0);
            if new_len > l {
                for _ in 0..(new_len - l) {
                    seq_push(&mut self.0, f());
                }
            } else {
                let _dropped = seq_drain(&mut self.0, new_len, l);
            }
        }
        /// See [`std::vec::Vec::retain`]
        pub fn retain<F: Fn(&T) -> bool>(&mut self, f: F) {
            let l = seq_len(&self.0);
            let mut rest = seq_drain(&mut self.0, 0, l);
            for _ in 0..l {
                let x = seq_remove(&mut rest, 0);
                if f(&x) {
                    seq_push(&mut self.0, x);
                }
            }
        }
        /// See [`std::vec::Vec::retain_mut`].
        //
        // DEVIATION(std): std's predicate takes `&mut T`, so it may rewrite the
        // elements it keeps. The model's `Fn*` traits are pure (`call_*` takes
        // `&self`, there is no write-back), so no closure in the model can
        // observe that difference and `retain_mut` coincides with `retain`.
        pub fn retain_mut<F: Fn(&T) -> bool>(&mut self, f: F) {
            self.retain(f)
        }
        /// See [`std::vec::Vec::from_fn`].
        //
        // Signature mirrors [`std::array::from_fn`] with an explicit length.
        pub fn from_fn<F: Fn(usize) -> T>(n: usize, f: F) -> Vec<T> {
            let mut out = seq_empty();
            for i in 0..n {
                seq_push(&mut out, f(i));
            }
            Vec(out)
        }
        /// See [`std::vec::Vec::extract_if`].
        //
        // DEVIATION(std): like `drain`, the range argument is ignored and the
        // whole vector is considered. Also, std's `ExtractIf` removes elements
        // lazily as it is iterated; the model removes them all up front, which
        // is indistinguishable once the iterator is dropped.
        pub fn extract_if<F: Fn(&T) -> bool, R /* : RangeBounds<usize> */>(
            &mut self,
            _range: R,
            filter: F,
        ) -> extract_if::ExtractIf<T> {
            let l = seq_len(&self.0);
            let mut rest = seq_drain(&mut self.0, 0, l);
            let mut extracted = seq_empty();
            for _ in 0..l {
                let x = seq_remove(&mut rest, 0);
                if filter(&x) {
                    seq_push(&mut extracted, x);
                } else {
                    seq_push(&mut self.0, x);
                }
            }
            extract_if::ExtractIf(extracted)
        }
    }
    pub mod drain {
        use rust_primitives::sequence::*;
        pub struct Drain<T, A>(pub Seq<T>, pub std::marker::PhantomData<A>);
        impl<T, A> Iterator for Drain<T, A> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    let res = seq_remove(&mut self.0, 0);
                    Option::Some(res)
                }
            }
        }
        impl<T, A> Drain<T, A> {
            /// See [`std::vec::Drain::as_slice`]
            pub fn as_slice(&self) -> &[T] {
                seq_to_slice(&self.0)
            }
        }
        impl<T> Drain<T, crate::alloc::Global> {
            /// See [`std::vec::Drain::allocator`]: `Vec::drain` only ever builds
            /// a globally-allocated `Drain` in the model. Returned by value,
            /// see `Vec::allocator`.
            pub fn allocator(&self) -> crate::alloc::Global {
                crate::alloc::Global
            }
        }
    }
    /// Model of `std::vec::ExtractIf`. Built eagerly by
    /// [`Vec::extract_if`]: it holds the elements the filter selected, already
    /// removed from the source `Vec`.
    pub mod extract_if {
        use rust_primitives::sequence::*;
        pub struct ExtractIf<T>(pub Seq<T>);
        impl<T> Iterator for ExtractIf<T> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    Option::Some(seq_remove(&mut self.0, 0))
                }
            }
        }
        impl<T> ExtractIf<T> {
            /// See [`std::vec::ExtractIf::allocator`]: see `Drain::allocator`.
            pub fn allocator(&self) -> crate::alloc::Global {
                crate::alloc::Global
            }
        }
    }

    #[hax_lib::attributes]
    impl<T: PartialEq> Vec<T> {
        /// See [`std::vec::Vec::dedup`]
        pub fn dedup(&mut self) {
            let l = seq_len(&self.0);
            let mut rest = seq_drain(&mut self.0, 0, l);
            for _ in 0..l {
                let x = seq_remove(&mut rest, 0);
                let n = seq_len(&self.0);
                // `is_dup`, not `keep`: a *materialized* `!b` is lowered to Lean's
                // `¬ b`, which is `Prop`, so the `if` below would have no
                // `Decidable` instance. Kept as an `if` condition instead, where
                // charon folds the negation into a branch swap and it stays a
                // `bool` (see also the `Neq` blanket impl in `core::cmp`).
                let is_dup = if n == 0 {
                    false
                } else {
                    PartialEq::eq(seq_index(&self.0, n - 1), &x)
                };
                if !is_dup {
                    seq_push(&mut self.0, x);
                }
            }
        }
    }

    #[hax_lib::attributes]
    impl<T> Vec<T> {
        /// See [`std::vec::Vec::dedup_by`]: `same_bucket(a, b)` is called with
        /// the candidate `a` and the last retained element `b`, and `a` is
        /// dropped when it returns `true`.
        //
        // DEVIATION(std): the predicate takes `&T` rather than `&mut T` — see
        // `retain_mut` for why the model cannot express the latter.
        pub fn dedup_by<F: Fn(&T, &T) -> bool>(&mut self, same_bucket: F) {
            let l = seq_len(&self.0);
            let mut rest = seq_drain(&mut self.0, 0, l);
            for _ in 0..l {
                let x = seq_remove(&mut rest, 0);
                let n = seq_len(&self.0);
                // See `dedup` for why this is not a negated `keep`.
                let is_dup = if n == 0 {
                    false
                } else {
                    same_bucket(&x, seq_index(&self.0, n - 1))
                };
                if !is_dup {
                    seq_push(&mut self.0, x);
                }
            }
        }
        /// See [`std::vec::Vec::dedup_by_key`]
        //
        // DEVIATION(std): `&T` rather than `&mut T`, see `dedup_by`.
        pub fn dedup_by_key<K: PartialEq, F: Fn(&T) -> K>(&mut self, key: F) {
            let l = seq_len(&self.0);
            let mut rest = seq_drain(&mut self.0, 0, l);
            for _ in 0..l {
                let x = seq_remove(&mut rest, 0);
                let n = seq_len(&self.0);
                // See `dedup` for why this is not a negated `keep`.
                let is_dup = if n == 0 {
                    false
                } else {
                    PartialEq::eq(&key(&x), &key(seq_index(&self.0, n - 1)))
                };
                if !is_dup {
                    seq_push(&mut self.0, x);
                }
            }
        }
    }

    #[hax_lib::attributes]
    impl<T, const N: usize> Vec<[T; N]> {
        /// See [`std::vec::Vec::into_flattened`]
        pub fn into_flattened(mut self) -> Vec<T> {
            let n = seq_len(&self.0);
            let mut out = seq_empty();
            for _ in 0..n {
                let mut chunk = seq_from_array(seq_remove(&mut self.0, 0));
                seq_concat(&mut out, &mut chunk);
            }
            Vec(out)
        }
    }

    // `resize` and `extend_from_slice` both require `T: Clone`, so real `alloc`
    // keeps them in the same `impl` block; keep them together here too so the
    // generated `impl_N__` prefix (`impl_2__resize`) matches what hax derives
    // from real `alloc`.
    #[hax_lib::attributes]
    impl<T: Clone> Vec<T> {
        #[hax_lib::requires(seq_len(&self.0).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(&mut self, other: &[T]) {
            seq_extend(&mut self.0, other)
        }
        // Like std's `extend_with`: `value` is cloned into all but the last new
        // slot, which takes `value` itself.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::ensures(|_| future(self).len() == new_size)]
        pub fn resize(&mut self, new_size: usize, value: T) {
            let l = seq_len(&self.0);
            if new_size > l {
                let mut extra = seq_create(value, new_size - l);
                seq_concat(&mut self.0, &mut extra);
            } else {
                seq_drain(&mut self.0, new_size, l);
            }
        }
        /// See [`std::vec::Vec::extend_from_within`].
        //
        // DEVIATION(std): like `drain`, the range argument is ignored and the
        // whole vector is appended to itself, so only `..` agrees with std.
        #[hax_lib::requires(seq_len(&self.0).to_int() + seq_len(&self.0).to_int() <= usize::MAX.to_int())]
        pub fn extend_from_within<R /* : RangeBounds<usize> */>(&mut self, _src: R) {
            let l = seq_len(&self.0);
            let mut copy = seq_empty();
            for i in 0..l {
                seq_push(&mut copy, seq_index(&self.0, i).clone());
            }
            seq_concat(&mut self.0, &mut copy) // TODO use range bounds
        }
    }

    /// Generic `Index<I>` impl for `Vec`, matching std's
    /// `impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A>`
    /// (in `alloc/src/vec/mod.rs`). Delegates through `Deref` to the
    /// `<[T]>::index` impl, the same body std uses. We omit the
    /// `A: Allocator` bound because we do not model `Allocator` as a
    /// trait — functionally identical for our purposes. The trait bound
    /// references `std::slice::SliceIndex` (the real one) rather than
    /// `core_models::slice::index::SliceIndex` because this crate is
    /// standalone and does not depend on `core_models`; Aeneas's name
    /// map for `std::slice::SliceIndex` aligns the extracted Lean path
    /// with `core_models`'s SliceIndex extraction (both extract under
    /// `core.slice.index.SliceIndex`).
    #[hax_lib::attributes]
    impl<T, I> std::ops::Index<I> for Vec<T>
    where
        I: std::slice::SliceIndex<[T]>,
    {
        type Output = I::Output;
        #[hax_lib::requires(self.get(i).is_some())]
        fn index(&self, i: I) -> &I::Output {
            std::ops::Index::index(&**self, i)
        }
    }

    /// Generic `IndexMut<I>` for `Vec`, mirroring the `Index<I>` impl above and
    /// std's `impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A>`,
    /// which routes through the mutable slice. Lean-only, like the slice
    /// `IndexMut` it delegates to. This is what `v[i] = x` extracts against.
    #[hax_lib::attributes]
    impl<T, I> std::ops::IndexMut<I> for Vec<T>
    where
        I: std::slice::SliceIndex<[T]>,
    {
        // Kept out of the Lean lane, as for the slice `IndexMut` it delegates to.
        #[cfg_attr(not(charon), hax_lib::requires(self.get(i).is_some()))]
        fn index_mut(&mut self, i: I) -> &mut I::Output {
            std::ops::IndexMut::index_mut(seq_to_slice_mut(&mut self.0), i)
        }
    }

    #[hax_lib::attributes]
    impl<T> core::ops::Deref for Vec<T> {
        type Target = [T];

        fn deref(&self) -> &[T] {
            self.as_slice()
        }
    }

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<T> std::iter::FromIterator<T> for Vec<T> {
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = T>,
        {
            let mut res = Vec::new();
            for el in iter {
                res.push(el)
            }
            res
        }
    }

    #[cfg(test)]
    mod tests;
}

// The F* backend keeps the explicit allocator type parameter `A` on `Vec`
#[cfg(hax_backend_fstar)]
pub mod vec {
    use crate::alloc::Global;
    use hax_lib::ToInt;
    use rust_primitives::sequence::*;
    use std::marker::PhantomData;

    // Unlike the default variant, this `Vec` models no `PartialEq`; the
    // derive is test-only (invisible to extraction) so that the shared test
    // suite in `vec_tests.rs` can compare models with `assert_eq!`.
    #[cfg_attr(test, derive(Debug, PartialEq))]
    #[hax_lib::fstar::before("open Rust_primitives.Notations")]
    pub struct Vec<T, A = Global>(pub Seq<T>, pub PhantomData<A>);

    /// See the `from_seq` in the non-F* `vec` module: same role, but threads
    /// the allocator parameter so external constructor sites are identical.
    pub(crate) fn from_seq<T, A>(s: Seq<T>) -> Vec<T, A> {
        Vec(s, PhantomData)
    }

    fn from_elem<T: Clone>(item: T, len: usize) -> Vec<T, Global> {
        Vec(seq_create(item, len), PhantomData)
    }

    #[hax_lib::attributes]
    impl<T> Vec<T, Global> {
        pub fn new() -> Vec<T, Global> {
            Vec(seq_empty(), PhantomData)
        }
        pub fn with_capacity(_c: usize) -> Vec<T, Global> {
            Vec::new()
        }
    }

    #[hax_lib::attributes]
    impl<T, A> Vec<T, A> {
        pub fn len(&self) -> usize {
            seq_len(&self.0)
        }
        #[hax_lib::requires(seq_len(&self.0) < usize::MAX)]
        pub fn push(&mut self, x: T) {
            seq_push(&mut self.0, x)
        }
        pub fn pop(&mut self) -> Option<T> {
            let l = seq_len(&self.0);
            if l > 0 {
                let last = seq_remove(&mut self.0, l - 1);
                Some(last)
            } else {
                None
            }
        }
        pub fn is_empty(&self) -> bool {
            seq_len(&self.0) == 0
        }
        #[hax_lib::requires(index <= seq_len(&self.0) && seq_len(&self.0) < usize::MAX)]
        pub fn insert(&mut self, index: usize, element: T) {
            let l = seq_len(&self.0);
            let mut right = seq_drain(&mut self.0, index, l);
            seq_push(&mut self.0, element);
            seq_concat(&mut self.0, &mut right);
        }
        pub fn as_slice(&self) -> &[T] {
            seq_to_slice(&self.0)
        }
        // These are opaque for F* only: a bare `#[hax_lib::opaque]` is invisible to
        // charon, so aeneas extracts the body regardless and it must model std.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn truncate(&mut self, n: usize) {
            let l = seq_len(&self.0);
            if n < l {
                seq_drain(&mut self.0, n, l);
            }
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::requires(n < self.len())]
        pub fn swap_remove(&mut self, n: usize) -> T {
            let l = seq_len(&self.0);
            let last = seq_remove(&mut self.0, l - 1);
            if n == l - 1 {
                last
            } else {
                let removed = seq_remove(&mut self.0, n);
                self.insert(n, last);
                removed
            }
        }
        /// `remove` drops one element, so it never grows the vector. The exact
        /// `len' = len - 1` would need `index < len` as a precondition (else on
        /// an empty vector it asserts a `usize` is `-1`), which callers holding
        /// only a length upper bound cannot discharge, so state the inequality.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::ensures(|_| future(self).len().to_int() <= self.len().to_int())]
        pub fn remove(&mut self, index: usize) -> T {
            seq_remove(&mut self.0, index)
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn clear(&mut self) {
            self.0 = seq_empty()
        }
        #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= usize::MAX.to_int())]
        pub fn append(&mut self, other: &mut Vec<T, A>) {
            seq_concat(&mut self.0, &mut other.0);
            other.0 = seq_empty()
        }
        /// See [`std::vec::Vec::split_off`]: truncate `self` to `[0, at)` and
        /// return the tail `[at, len)` as a new `Vec`.
        #[hax_lib::requires(at <= self.len())]
        pub fn split_off(&mut self, at: usize) -> Vec<T, A> {
            let l = seq_len(&self.0);
            Vec(seq_drain(&mut self.0, at, l), PhantomData)
        }
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        pub fn drain<R /* : RangeBounds<usize> */>(&mut self, _range: R) -> drain::Drain<T, A> {
            let l = seq_len(&self.0);
            drain::Drain(seq_drain(&mut self.0, 0, l), PhantomData) // TODO use range bounds
        }
    }

    pub mod into_iter {
        use rust_primitives::sequence::*;
        pub struct IntoIter<T>(pub Seq<T>);
        impl<T> Iterator for IntoIter<T> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
        }
    }
    pub mod drain {
        use rust_primitives::sequence::*;
        pub struct Drain<T, A>(pub Seq<T>, pub std::marker::PhantomData<A>);
        impl<T, A> Iterator for Drain<T, A> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    let res = seq_remove(&mut self.0, 0);
                    Option::Some(res)
                }
            }
        }
    }

    // `resize` and `extend_from_slice` both require `T: Clone`, so real `alloc`
    // keeps them in the same `impl` block; keep them together here too so the
    // generated `impl_N__` prefix (`impl_2__resize`) matches what hax derives
    // from real `alloc`.
    #[hax_lib::attributes]
    impl<T: Clone, A> Vec<T, A> {
        #[hax_lib::requires(seq_len(&self.0).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(&mut self, other: &[T]) {
            seq_extend(&mut self.0, other)
        }
        // Like std's `extend_with`: `value` is cloned into all but the last new
        // slot, which takes `value` itself.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::ensures(|_| future(self).len() == new_size)]
        pub fn resize(&mut self, new_size: usize, value: T) {
            let l = seq_len(&self.0);
            if new_size > l {
                let mut extra = seq_create(value, new_size - l);
                seq_concat(&mut self.0, &mut extra);
            } else {
                seq_drain(&mut self.0, new_size, l);
            }
        }
    }

    /// Generic `Index<I>` impl, mirroring std's
    /// `impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A>`.
    #[hax_lib::attributes]
    impl<T, I, A> std::ops::Index<I> for Vec<T, A>
    where
        I: std::slice::SliceIndex<[T]>,
    {
        type Output = I::Output;
        #[hax_lib::requires(self.get(i).is_some())]
        fn index(&self, i: I) -> &I::Output {
            std::ops::Index::index(&**self, i)
        }
    }

    #[hax_lib::attributes]
    impl<T, A> core::ops::Deref for Vec<T, A> {
        type Target = [T];

        fn deref(&self) -> &[T] {
            self.as_slice()
        }
    }

    #[hax_lib::attributes]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<T> std::iter::FromIterator<T> for Vec<T, Global> {
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = T>,
        {
            let mut res = Vec::new();
            for el in iter {
                res.push(el)
            }
            res
        }
    }

    #[cfg(test)]
    mod tests;
}
