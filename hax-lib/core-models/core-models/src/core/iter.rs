// This model of iterators doesn't respect the signatures of the original definitions in Rust core.
// We avoid default implementations for trait methods, and instead provide them as external to the trait.
// This means overriding them is not possible.
// We also avoid the coinductivity between `IntoIter` and `Iterator`.

pub mod traits {
    pub mod iterator {
        use super::super::adapters::{
            array_chunks::ArrayChunks, chain::Chain, cloned::Cloned, copied::Copied, cycle::Cycle,
            enumerate::Enumerate, filter::Filter, filter_map::FilterMap, flat_map::FlatMap,
            flatten::Flatten, fuse::Fuse, inspect::Inspect, intersperse::Intersperse,
            intersperse::IntersperseWith, map::Map, map_while::MapWhile, map_windows::MapWindows,
            peekable::Peekable, rev::Rev, skip::Skip, skip_while::SkipWhile, step_by::StepBy,
            take::Take, take_while::TakeWhile, zip::Zip,
        };
        use super::accum::{Product, Sum};
        use super::collect::Extend;
        use super::double_ended::DoubleEndedIterator;
        use super::exact_size::ExactSizeIterator;
        use crate::cmp::Ordering;
        use crate::default::Default;
        use crate::ops::control_flow::ControlFlow;
        use crate::ops::try_trait::{FromResidual, Residual, Try};
        use crate::option::Option;
        use crate::result::Result;
        use rust_primitives::sequence::{Seq, seq_empty, seq_index, seq_len, seq_push, seq_remove};
        use rust_primitives::slice::array_from_fn;
        /// See [`std::iter::Iterator`]
        #[hax_lib::attributes]
        pub trait Iterator {
            type Item;
            #[hax_lib::requires(true)]
            fn next(&mut self) -> Option<Self::Item>;
        }

        // This trait is an addition to deal with the default methods that the F* backend doesn't handle
        #[hax_lib::attributes]
        pub(crate) trait IteratorMethods: Iterator {
            fn fold<B, F: Fn(B, Self::Item) -> B>(self, init: B, f: F) -> B;
            fn enumerate(self) -> Enumerate<Self>
            where
                Self: Sized;
            #[hax_lib::requires(step > 0)]
            fn step_by(self, step: usize) -> StepBy<Self>
            where
                Self: Sized;
            fn map<O, F: Fn(Self::Item) -> O>(self, f: F) -> Map<Self, F>
            where
                Self: Sized;
            fn all<F: Fn(Self::Item) -> bool>(self, f: F) -> bool;
            fn take(self, n: usize) -> Take<Self>
            where
                Self: Sized;
            fn flat_map<U: Iterator, F: Fn(Self::Item) -> U>(self, f: F) -> FlatMap<Self, U, F>
            where
                Self: Sized;
            fn flatten(self) -> Flatten<Self>
            where
                Self::Item: Iterator,
                Self: Sized;
            fn zip<I2: Iterator>(self, it2: I2) -> Zip<Self, I2>
            where
                Self: Sized;
            fn filter<P: Fn(&Self::Item) -> bool>(self, predicate: P) -> Filter<Self, P>
            where
                Self: Sized;
            fn chain<U: Iterator<Item = Self::Item>>(self, other: U) -> Chain<Self, U>
            where
                Self: Sized;
            fn skip(self, n: usize) -> Skip<Self>
            where
                Self: Sized;
            fn any<F: Fn(Self::Item) -> bool>(self, f: F) -> bool;
            fn find<P: Fn(&Self::Item) -> bool>(self, predicate: P) -> Option<Self::Item>;
            fn find_map<B, F: Fn(Self::Item) -> Option<B>>(self, f: F) -> Option<B>;
            fn position<P: Fn(Self::Item) -> bool>(self, predicate: P) -> Option<usize>;
            fn count(self) -> usize;
            fn nth(self, n: usize) -> Option<Self::Item>;
            fn last(self) -> Option<Self::Item>;
            fn for_each<F: Fn(Self::Item)>(self, f: F);
            fn reduce<F: Fn(Self::Item, Self::Item) -> Self::Item>(
                self,
                f: F,
            ) -> Option<Self::Item>;
            fn min(self) -> Option<Self::Item>
            where
                Self::Item: crate::cmp::Ord;
            fn max(self) -> Option<Self::Item>
            where
                Self::Item: crate::cmp::Ord;
            fn collect<B: super::super::traits::collect::FromIterator<Self::Item>>(self) -> B
            where
                Self: Sized;
            fn rev(self) -> Rev<Self>
            where
                Self: Sized + DoubleEndedIterator;
            // The methods gated out of the F* model below delegate to a helper
            // that needs extra instance arguments (`ExactSizeIterator`,
            // `Default`/`Extend`, `Ord`, `Clone`, `Try`/`Residual`, …). hax emits
            // the call without them and F*'s typeclass resolution cannot recover
            // them, so the whole blanket impl stops typechecking. They stay in the
            // Rust model and in the Lean extraction.
            #[cfg(not(hax_backend_fstar))]
            fn rposition<P: Fn(Self::Item) -> bool>(&mut self, predicate: P) -> Option<usize>
            where
                Self: Sized + ExactSizeIterator + DoubleEndedIterator;
            /// The residual count is a plain `usize` (always non-zero on `Err`)
            /// because the model has no `core::num::NonZero`.
            fn advance_by(&mut self, n: usize) -> crate::result::Result<(), usize>;
            fn cloned<'a, T: Clone + 'a>(self) -> Cloned<Self>
            where
                Self: Sized + Iterator<Item = &'a T>;
            fn copied<'a, T: Copy + 'a>(self) -> Copied<Self>
            where
                Self: Sized + Iterator<Item = &'a T>;
            fn inspect<F: Fn(&Self::Item)>(self, f: F) -> Inspect<Self, F>
            where
                Self: Sized;
            fn filter_map<B, F: Fn(Self::Item) -> Option<B>>(self, f: F) -> FilterMap<Self, F>
            where
                Self: Sized;
            fn map_while<B, P: Fn(Self::Item) -> Option<B>>(
                self,
                predicate: P,
            ) -> MapWhile<Self, P>
            where
                Self: Sized;
            fn skip_while<P: Fn(&Self::Item) -> bool>(self, predicate: P) -> SkipWhile<Self, P>
            where
                Self: Sized;
            fn take_while<P: Fn(&Self::Item) -> bool>(self, predicate: P) -> TakeWhile<Self, P>
            where
                Self: Sized;
            // Not part of the F* model: hax rejects the `Fn(&mut _, _)` bound
            // (HAX0003 `DirectAndMut`, hacspec/hax#420).
            #[cfg(not(hax_backend_fstar))]
            fn scan<St, B, F: Fn(&mut St, Self::Item) -> Option<B>>(
                self,
                initial_state: St,
                f: F,
            ) -> super::super::adapters::scan::Scan<Self, St, F>
            where
                Self: Sized;
            fn fuse(self) -> Fuse<Self>
            where
                Self: Sized;
            fn cycle(self) -> Cycle<Self>
            where
                Self: Sized + Clone;
            fn peekable(self) -> Peekable<Self>
            where
                Self: Sized;
            fn intersperse(self, separator: Self::Item) -> Intersperse<Self>
            where
                Self: Sized,
                Self::Item: Clone;
            fn intersperse_with<G: Fn() -> Self::Item>(
                self,
                separator: G,
            ) -> IntersperseWith<Self, G>
            where
                Self: Sized;
            #[hax_lib::requires(N != 0)]
            fn array_chunks<const N: usize>(self) -> ArrayChunks<Self, N>
            where
                Self: Sized;
            #[hax_lib::requires(N != 0)]
            fn map_windows<R, F: Fn(&[Self::Item; N]) -> R, const N: usize>(
                self,
                f: F,
            ) -> MapWindows<Self, F, N>
            where
                Self: Sized;
            // Not part of the F* model: hax rejects returning a `&mut` that was
            // passed in (HAX0003 `DirectAndMut` / HAX0010, hacspec/hax#420).
            #[cfg(not(hax_backend_fstar))]
            fn by_ref(&mut self) -> &mut Self
            where
                Self: Sized;
            /// The model's `Iterator` has no way to report a tighter bound, so
            /// this is std's default answer, `(0, None)`. That is always a valid
            /// size hint (the contract only asks for a correct lower bound and an
            /// optional upper bound), just an uninformative one.
            fn size_hint(&self) -> (usize, Option<usize>);
            // `sum`, `product` and the comparison family below
            // (`cmp`/`partial_cmp`/`eq`/`lt`/`le`/`gt`/`ge`) are not part of the
            // F* model. hax names a trait method's contract lemmas after the
            // method alone (`f_sum_pre`, `f_cmp_pre`, …) and puts every trait in
            // `core_models` into one `Core_models.Bundle` module, so a method
            // whose name is also a method of another trait in the crate is a
            // duplicate top-level name there. These nine clash with
            // `iter::traits::accum::{Sum::sum, Product::product}` and
            // `cmp::{Ord::cmp, PartialOrd::partial_cmp, PartialEq::eq,
            // PartialOrdDefaults::{lt, le, gt, ge}}`, which the F* library needs
            // far more than the iterator conveniences do. The `_by` variants and
            // `ne` have no counterpart elsewhere and stay.
            #[cfg(not(hax_backend_fstar))]
            fn sum<S: Sum<Self::Item>>(self) -> S
            where
                Self: Sized;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn product<P: Product<Self::Item>>(self) -> P
            where
                Self: Sized;
            fn min_by<F: Fn(&Self::Item, &Self::Item) -> Ordering>(
                self,
                compare: F,
            ) -> Option<Self::Item>;
            fn max_by<F: Fn(&Self::Item, &Self::Item) -> Ordering>(
                self,
                compare: F,
            ) -> Option<Self::Item>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn min_by_key<B: crate::cmp::Ord, F: Fn(&Self::Item) -> B>(
                self,
                f: F,
            ) -> Option<Self::Item>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn max_by_key<B: crate::cmp::Ord, F: Fn(&Self::Item) -> B>(
                self,
                f: F,
            ) -> Option<Self::Item>;
            // The `cmp`/`eq`/ordering family takes an `Iterator` rather than
            // std's `IntoIterator`, matching `IteratorMethods::chain`: the model's
            // `IntoIterator` deliberately does not bound `IntoIter: Iterator`.
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn cmp<I2: Iterator<Item = Self::Item>>(self, other: I2) -> Ordering
            where
                Self: Sized,
                Self::Item: crate::cmp::Ord;
            fn cmp_by<I2: Iterator, F: Fn(Self::Item, I2::Item) -> Ordering>(
                self,
                other: I2,
                cmp: F,
            ) -> Ordering
            where
                Self: Sized;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn partial_cmp<I2: Iterator>(self, other: I2) -> Option<Ordering>
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<I2::Item>;
            fn partial_cmp_by<I2: Iterator, F: Fn(Self::Item, I2::Item) -> Option<Ordering>>(
                self,
                other: I2,
                partial_cmp: F,
            ) -> Option<Ordering>
            where
                Self: Sized;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn eq<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialEq<I2::Item>;
            fn eq_by<I2: Iterator, F: Fn(Self::Item, I2::Item) -> bool>(
                self,
                other: I2,
                eq: F,
            ) -> bool
            where
                Self: Sized;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn ne<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialEq<I2::Item>;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn lt<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<I2::Item>;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn le<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<I2::Item>;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn gt<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<I2::Item>;
            // Not part of the F* model, see the note on `sum` above.
            #[cfg(not(hax_backend_fstar))]
            fn ge<I2: Iterator>(self, other: I2) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<I2::Item>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn unzip<A, B, FromA: Default + Extend<A>, FromB: Default + Extend<B>>(
                self,
            ) -> (FromA, FromB)
            where
                Self: Sized + Iterator<Item = (A, B)>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn partition<B: Default + Extend<Self::Item>, F: Fn(&Self::Item) -> bool>(
                self,
                f: F,
            ) -> (B, B)
            where
                Self: Sized;
            fn is_partitioned<P: Fn(Self::Item) -> bool>(self, predicate: P) -> bool
            where
                Self: Sized;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn is_sorted(self) -> bool
            where
                Self: Sized,
                Self::Item: crate::cmp::PartialOrd<Self::Item>;
            fn is_sorted_by<F: Fn(&Self::Item, &Self::Item) -> bool>(self, compare: F) -> bool
            where
                Self: Sized;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn is_sorted_by_key<K: crate::cmp::PartialOrd<K>, F: Fn(Self::Item) -> K>(
                self,
                f: F,
            ) -> bool
            where
                Self: Sized;
            // Not part of the F* model: hax rejects returning a `&mut` that was
            // passed in (HAX0003 `DirectAndMut` / HAX0010, hacspec/hax#420).
            #[cfg(not(hax_backend_fstar))]
            fn collect_into<E: Extend<Self::Item>>(self, collection: &mut E) -> &mut E
            where
                Self: Sized;
            /// The `Item: Clone` bound is a deviation: std assembles the `[Item; N]`
            /// through `MaybeUninit`, which the model has no counterpart for.
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn next_chunk<const N: usize>(
                &mut self,
            ) -> Result<[Self::Item; N], crate::array::iter::IntoIter<Self::Item, N>>
            where
                Self: Sized,
                Self::Item: Clone;
            /// `R: FromResidual<R::Residual>` is a deviation: std gets it from
            /// `Try`'s supertrait, which the model's `ops::try_trait::Try` lacks.
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn try_fold<
                B,
                R: Try<Output = B> + FromResidual<<R as Try>::Residual>,
                F: Fn(B, Self::Item) -> R,
            >(
                &mut self,
                init: B,
                f: F,
            ) -> R
            where
                Self: Sized;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn try_for_each<
                R: Try<Output = ()> + FromResidual<<R as Try>::Residual>,
                F: Fn(Self::Item) -> R,
            >(
                &mut self,
                f: F,
            ) -> R
            where
                Self: Sized;
            /// std spells the return type `ChangeOutputType<R, Option<Self::Item>>`;
            /// that alias expands to exactly the projection written out here. The
            /// extra `TryType: FromResidual<..>` bound is the same deviation as on
            /// `try_fold`.
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn try_find<R, F: Fn(&Self::Item) -> R>(
                &mut self,
                f: F,
            ) -> <<R as Try>::Residual as Residual<Option<Self::Item>>>::TryType
            where
                Self: Sized,
                R: Try<Output = bool>,
                <R as Try>::Residual: Residual<Option<Self::Item>>,
                <<R as Try>::Residual as Residual<Option<Self::Item>>>::TryType:
                    FromResidual<<R as Try>::Residual>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn try_reduce<R, F: Fn(Self::Item, Self::Item) -> R>(
                &mut self,
                f: F,
            ) -> <<R as Try>::Residual as Residual<Option<Self::Item>>>::TryType
            where
                Self: Sized,
                R: Try<Output = Self::Item>,
                <R as Try>::Residual: Residual<Option<Self::Item>>,
                <<R as Try>::Residual as Residual<Option<Self::Item>>>::TryType:
                    FromResidual<<R as Try>::Residual>;
            // Not in the F* model, see the note on `rposition` above.
            #[cfg(not(hax_backend_fstar))]
            fn try_collect<B>(&mut self) -> <<Self::Item as Try>::Residual as Residual<B>>::TryType
            where
                Self: Sized,
                Self::Item: Try,
                <Self::Item as Try>::Residual: Residual<B>,
                B: super::collect::FromIterator<<Self::Item as Try>::Output>,
                <<Self::Item as Try>::Residual as Residual<B>>::TryType:
                    FromResidual<<Self::Item as Try>::Residual>;
        }

        // Opaque helper functions for loop-based iterator methods.
        // #[hax_lib::opaque] only works at the function/impl-block level, not on individual
        // methods within an impl block, so we use standalone functions and delegate.

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_fold<I: Iterator, B, F: Fn(B, I::Item) -> B>(mut iter: I, init: B, f: F) -> B {
            let mut accum = init;
            while let Option::Some(x) = iter.next() {
                accum = f(accum, x);
            }
            accum
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_all<I: Iterator, F: Fn(I::Item) -> bool>(mut iter: I, f: F) -> bool {
            while let Option::Some(x) = iter.next() {
                if !f(x) {
                    return false;
                }
            }
            true
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_any<I: Iterator, F: Fn(I::Item) -> bool>(mut iter: I, f: F) -> bool {
            while let Option::Some(x) = iter.next() {
                if f(x) {
                    return true;
                }
            }
            false
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_find<I: Iterator, P: Fn(&I::Item) -> bool>(
            iter: &mut I,
            predicate: P,
        ) -> Option<I::Item> {
            while let Option::Some(x) = iter.next() {
                if predicate(&x) {
                    return Option::Some(x);
                }
            }
            Option::None
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_find_map<I: Iterator, B, F: Fn(I::Item) -> Option<B>>(
            mut iter: I,
            f: F,
        ) -> Option<B> {
            while let Option::Some(x) = iter.next() {
                if let Option::Some(v) = f(x) {
                    return Option::Some(v);
                }
            }
            Option::None
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_position<I: Iterator, P: Fn(I::Item) -> bool>(
            mut iter: I,
            predicate: P,
        ) -> Option<usize> {
            let mut i: usize = 0;
            while let Option::Some(x) = iter.next() {
                if predicate(x) {
                    return Option::Some(i);
                }
                i += 1;
            }
            Option::None
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_count<I: Iterator>(mut iter: I) -> usize {
            let mut n: usize = 0;
            while let Option::Some(_) = iter.next() {
                n += 1;
            }
            n
        }

        // opaque: for-loop generates Rust_primitives.Hax.Folds, causing F* dependency cycle
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[cfg_attr(charon, hax_lib::exclude)] // forward reference in lean (`core.Usize.Insts.CoreIterRangeStep`)
        fn iter_nth<I: Iterator>(mut iter: I, n: usize) -> Option<I::Item> {
            for _ in 0..n {
                if let Option::None = iter.next() {
                    return Option::None;
                }
            }
            iter.next()
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_last<I: Iterator>(mut iter: I) -> Option<I::Item> {
            let mut last = Option::None;
            while let Option::Some(x) = iter.next() {
                last = Option::Some(x);
            }
            last
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_for_each<I: Iterator, F: Fn(I::Item)>(mut iter: I, f: F) {
            while let Option::Some(x) = iter.next() {
                f(x);
            }
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_reduce<I: Iterator, F: Fn(I::Item, I::Item) -> I::Item>(
            mut iter: I,
            f: F,
        ) -> Option<I::Item> {
            let mut accum = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            while let Option::Some(x) = iter.next() {
                accum = f(accum, x);
            }
            Option::Some(accum)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_min<I: Iterator>(mut iter: I) -> Option<I::Item>
        where
            I::Item: crate::cmp::Ord,
        {
            let mut min = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            while let Option::Some(x) = iter.next() {
                if let crate::cmp::Ordering::Less = crate::cmp::Ord::cmp(&x, &min) {
                    min = x;
                }
            }
            Option::Some(min)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        fn iter_max<I: Iterator>(mut iter: I) -> Option<I::Item>
        where
            I::Item: crate::cmp::Ord,
        {
            let mut max = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            while let Option::Some(x) = iter.next() {
                if let crate::cmp::Ordering::Greater = crate::cmp::Ord::cmp(&x, &max) {
                    max = x;
                }
            }
            Option::Some(max)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        // aeneas: reborrowing `&mut I` as `&I` for `ExactSizeIterator::len` trips
        // its type checker ("new value doesn't have the same type as its
        // destination"). Nothing outside the (also excluded) `IteratorMethods`
        // blanket impl refers to this helper.
        #[cfg_attr(charon, aeneas::exclude)]
        fn iter_rposition<I: ExactSizeIterator + DoubleEndedIterator, P: Fn(I::Item) -> bool>(
            iter: &mut I,
            predicate: P,
        ) -> Option<usize> {
            let mut i = ExactSizeIterator::len(iter);
            while let Option::Some(x) = iter.next_back() {
                i -= 1;
                if predicate(x) {
                    return Option::Some(i);
                }
            }
            Option::None
        }

        // opaque: while-loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_advance_by<I: Iterator>(
            iter: &mut I,
            n: usize,
        ) -> crate::result::Result<(), usize> {
            let mut remaining = n;
            while remaining > 0 {
                match iter.next() {
                    Option::None => return crate::result::Result::Err(remaining),
                    Option::Some(_) => remaining -= 1,
                }
            }
            crate::result::Result::Ok(())
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_min_by<I: Iterator, F: Fn(&I::Item, &I::Item) -> Ordering>(
            mut iter: I,
            compare: F,
        ) -> Option<I::Item> {
            let mut best = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            // Ties keep the earlier element, as std's `cmp::min_by` does.
            while let Option::Some(x) = iter.next() {
                if let Ordering::Less = compare(&x, &best) {
                    best = x;
                }
            }
            Option::Some(best)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_max_by<I: Iterator, F: Fn(&I::Item, &I::Item) -> Ordering>(
            mut iter: I,
            compare: F,
        ) -> Option<I::Item> {
            let mut best = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            // Ties keep the *later* element, as std's `cmp::max_by` does.
            while let Option::Some(x) = iter.next() {
                match compare(&x, &best) {
                    Ordering::Less => (),
                    _ => best = x,
                }
            }
            Option::Some(best)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_min_by_key<I: Iterator, B: crate::cmp::Ord, F: Fn(&I::Item) -> B>(
            mut iter: I,
            f: F,
        ) -> Option<I::Item> {
            let mut best = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            let mut best_key = f(&best);
            while let Option::Some(x) = iter.next() {
                let key = f(&x);
                if let Ordering::Less = crate::cmp::Ord::cmp(&key, &best_key) {
                    best = x;
                    best_key = key;
                }
            }
            Option::Some(best)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_max_by_key<I: Iterator, B: crate::cmp::Ord, F: Fn(&I::Item) -> B>(
            mut iter: I,
            f: F,
        ) -> Option<I::Item> {
            let mut best = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Option::None,
            };
            let mut best_key = f(&best);
            while let Option::Some(x) = iter.next() {
                let key = f(&x);
                match crate::cmp::Ord::cmp(&key, &best_key) {
                    Ordering::Less => (),
                    _ => {
                        best = x;
                        best_key = key;
                    }
                }
            }
            Option::Some(best)
        }

        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        // The comparator is `compare`, not std's `cmp`: a binder named `cmp`
        // shadows the `core.cmp` namespace in the Lean extraction, so the
        // `Ordering` references in this body stop resolving.
        fn iter_cmp_by<I1: Iterator, I2: Iterator, F: Fn(I1::Item, I2::Item) -> Ordering>(
            mut a: I1,
            mut b: I2,
            compare: F,
        ) -> Ordering {
            loop {
                match a.next() {
                    Option::None => {
                        return match b.next() {
                            Option::None => Ordering::Equal,
                            Option::Some(_) => Ordering::Less,
                        };
                    }
                    Option::Some(x) => match b.next() {
                        Option::None => return Ordering::Greater,
                        Option::Some(y) => match compare(x, y) {
                            Ordering::Equal => (),
                            non_eq => return non_eq,
                        },
                    },
                }
            }
        }

        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_partial_cmp_by<
            I1: Iterator,
            I2: Iterator,
            F: Fn(I1::Item, I2::Item) -> Option<Ordering>,
        >(
            mut a: I1,
            mut b: I2,
            partial_cmp: F,
        ) -> Option<Ordering> {
            loop {
                match a.next() {
                    Option::None => {
                        return match b.next() {
                            Option::None => Option::Some(Ordering::Equal),
                            Option::Some(_) => Option::Some(Ordering::Less),
                        };
                    }
                    Option::Some(x) => match b.next() {
                        Option::None => return Option::Some(Ordering::Greater),
                        Option::Some(y) => match partial_cmp(x, y) {
                            Option::Some(Ordering::Equal) => (),
                            non_eq => return non_eq,
                        },
                    },
                }
            }
        }

        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_eq_by<I1: Iterator, I2: Iterator, F: Fn(I1::Item, I2::Item) -> bool>(
            mut a: I1,
            mut b: I2,
            eq: F,
        ) -> bool {
            loop {
                match a.next() {
                    Option::None => {
                        return match b.next() {
                            Option::None => true,
                            Option::Some(_) => false,
                        };
                    }
                    Option::Some(x) => match b.next() {
                        Option::None => return false,
                        Option::Some(y) => {
                            if eq(x, y) == false {
                                return false;
                            }
                        }
                    },
                }
            }
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_unzip<
            I: Iterator<Item = (A, B)>,
            A,
            B,
            FromA: Default + Extend<A>,
            FromB: Default + Extend<B>,
        >(
            mut iter: I,
        ) -> (FromA, FromB) {
            let mut left = FromA::default();
            let mut right = FromB::default();
            while let Option::Some((x, y)) = iter.next() {
                left.extend(super::super::sources::once::once(x));
                right.extend(super::super::sources::once::once(y));
            }
            (left, right)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_partition<I: Iterator, B: Default + Extend<I::Item>, F: Fn(&I::Item) -> bool>(
            mut iter: I,
            f: F,
        ) -> (B, B) {
            let mut yes = B::default();
            let mut no = B::default();
            while let Option::Some(x) = iter.next() {
                if f(&x) {
                    yes.extend(super::super::sources::once::once(x));
                } else {
                    no.extend(super::super::sources::once::once(x));
                }
            }
            (yes, no)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_is_partitioned<I: Iterator, P: Fn(I::Item) -> bool>(
            mut iter: I,
            predicate: P,
        ) -> bool {
            let mut seen_false = false;
            while let Option::Some(x) = iter.next() {
                if predicate(x) {
                    if seen_false {
                        return false;
                    }
                } else {
                    seen_false = true;
                }
            }
            true
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_is_sorted_by<I: Iterator, F: Fn(&I::Item, &I::Item) -> bool>(
            mut iter: I,
            compare: F,
        ) -> bool {
            let mut prev = match iter.next() {
                Option::Some(x) => x,
                Option::None => return true,
            };
            while let Option::Some(x) = iter.next() {
                if compare(&prev, &x) == false {
                    return false;
                }
                prev = x;
            }
            true
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_next_chunk<I: Iterator, const N: usize>(
            iter: &mut I,
        ) -> Result<[I::Item; N], crate::array::iter::IntoIter<I::Item, N>>
        where
            I::Item: Clone,
        {
            let mut buf = seq_empty();
            while seq_len(&buf) < N {
                match iter.next() {
                    Option::Some(v) => seq_push(&mut buf, v),
                    Option::None => return Result::Err(crate::array::iter::IntoIter(buf)),
                }
            }
            Result::Ok(array_from_fn(|i| seq_index(&buf, i).clone()))
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_fold<
            I: Iterator,
            B,
            R: Try<Output = B> + FromResidual<<R as Try>::Residual>,
            F: Fn(B, I::Item) -> R,
        >(
            iter: &mut I,
            init: B,
            f: F,
        ) -> R {
            let mut accum = init;
            while let Option::Some(x) = iter.next() {
                match Try::branch(f(accum, x)) {
                    ControlFlow::Continue(v) => accum = v,
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(accum)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_for_each<
            I: Iterator,
            R: Try<Output = ()> + FromResidual<<R as Try>::Residual>,
            F: Fn(I::Item) -> R,
        >(
            iter: &mut I,
            f: F,
        ) -> R {
            while let Option::Some(x) = iter.next() {
                match Try::branch(f(x)) {
                    ControlFlow::Continue(_) => (),
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(())
        }

        /// A `Seq`-backed iterator, used only to hand `try_collect`'s successful
        /// outputs to `FromIterator`. Not a `core` item: the model has no public
        /// iterator over a `rust_primitives` sequence.
        struct SeqIter<T>(Seq<T>);

        // Excluded from coverage: `FromIterator::from_iter` cannot walk its
        // argument (its `T: IntoIterator` bound does not require
        // `T::IntoIter: Iterator`), so nothing in the model ever pulls from this.
        #[cfg_attr(coverage_nightly, coverage(off))]
        impl<T> Iterator for SeqIter<T> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    Option::Some(seq_remove(&mut self.0, 0))
                }
            }
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_find<I: Iterator, R: Try<Output = bool>, F: Fn(&I::Item) -> R>(
            iter: &mut I,
            f: F,
        ) -> <<R as Try>::Residual as Residual<Option<I::Item>>>::TryType
        where
            <R as Try>::Residual: Residual<Option<I::Item>>,
            <<R as Try>::Residual as Residual<Option<I::Item>>>::TryType:
                FromResidual<<R as Try>::Residual>,
        {
            while let Option::Some(x) = iter.next() {
                match Try::branch(f(&x)) {
                    ControlFlow::Continue(found) => {
                        if found {
                            return Try::from_output(Option::Some(x));
                        }
                    }
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(Option::None)
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_reduce<I: Iterator, R: Try<Output = I::Item>, F: Fn(I::Item, I::Item) -> R>(
            iter: &mut I,
            f: F,
        ) -> <<R as Try>::Residual as Residual<Option<I::Item>>>::TryType
        where
            <R as Try>::Residual: Residual<Option<I::Item>>,
            <<R as Try>::Residual as Residual<Option<I::Item>>>::TryType:
                FromResidual<<R as Try>::Residual>,
        {
            let mut accum = match iter.next() {
                Option::Some(x) => x,
                Option::None => return Try::from_output(Option::None),
            };
            while let Option::Some(x) = iter.next() {
                match Try::branch(f(accum, x)) {
                    ControlFlow::Continue(v) => accum = v,
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(Option::Some(accum))
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_collect<I: Iterator, B>(
            iter: &mut I,
        ) -> <<I::Item as Try>::Residual as Residual<B>>::TryType
        where
            I::Item: Try,
            <I::Item as Try>::Residual: Residual<B>,
            B: super::collect::FromIterator<<I::Item as Try>::Output>,
            <<I::Item as Try>::Residual as Residual<B>>::TryType:
                FromResidual<<I::Item as Try>::Residual>,
        {
            let mut out = seq_empty();
            while let Option::Some(x) = iter.next() {
                match Try::branch(x) {
                    ControlFlow::Continue(v) => seq_push(&mut out, v),
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(super::collect::FromIterator::from_iter(SeqIter(out)))
        }

        #[hax_lib::attributes]
        #[cfg_attr(charon, hax_lib::exclude)]
        // `Item` reaches this impl through `IteratorMethods`' supertrait, which
        // hax cannot qualify on its own, so it is spelled out as
        // `<I as Iterator>::Item` throughout (cryspen/hax#2089).
        impl<I: Iterator> IteratorMethods for I {
            fn fold<B, F: Fn(B, I::Item) -> B>(self, init: B, f: F) -> B {
                iter_fold(self, init, f)
            }

            fn enumerate(self) -> Enumerate<I> {
                Enumerate::new(self)
            }

            #[hax_lib::requires(step > 0)]
            fn step_by(self, step: usize) -> StepBy<I> {
                StepBy::new(self, step)
            }

            fn map<O, F: Fn(I::Item) -> O>(self, f: F) -> Map<I, F> {
                Map::new(self, f)
            }

            fn all<F: Fn(I::Item) -> bool>(self, f: F) -> bool {
                iter_all(self, f)
            }

            fn take(self, n: usize) -> Take<I> {
                Take::new(self, n)
            }

            fn flat_map<U: Iterator, F: Fn(I::Item) -> U>(self, f: F) -> FlatMap<I, U, F> {
                FlatMap::new(self, f)
            }

            fn flatten(self) -> Flatten<I>
            where
                I::Item: Iterator,
            {
                Flatten::new(self)
            }

            fn zip<I2: Iterator>(self, it2: I2) -> Zip<Self, I2> {
                Zip::new(self, it2)
            }

            fn filter<P: Fn(&<I as Iterator>::Item) -> bool>(
                self,
                predicate: P,
            ) -> Filter<Self, P> {
                Filter::new(self, predicate)
            }

            fn chain<U: Iterator<Item = <I as Iterator>::Item>>(self, other: U) -> Chain<Self, U> {
                Chain::new(self, other)
            }

            fn skip(self, n: usize) -> Skip<Self> {
                Skip::new(self, n)
            }

            fn any<F: Fn(<I as Iterator>::Item) -> bool>(self, f: F) -> bool {
                iter_any(self, f)
            }

            fn find<P: Fn(&<I as Iterator>::Item) -> bool>(
                mut self,
                predicate: P,
            ) -> Option<<I as Iterator>::Item> {
                iter_find(&mut self, predicate)
            }

            fn find_map<B, F: Fn(<I as Iterator>::Item) -> Option<B>>(self, f: F) -> Option<B> {
                iter_find_map(self, f)
            }

            fn position<P: Fn(<I as Iterator>::Item) -> bool>(self, predicate: P) -> Option<usize> {
                iter_position(self, predicate)
            }

            fn count(self) -> usize {
                iter_count(self)
            }

            fn nth(self, n: usize) -> Option<<I as Iterator>::Item> {
                iter_nth(self, n)
            }

            fn last(self) -> Option<<I as Iterator>::Item> {
                iter_last(self)
            }

            fn for_each<F: Fn(<I as Iterator>::Item)>(self, f: F) {
                iter_for_each(self, f)
            }

            fn reduce<
                F: Fn(<I as Iterator>::Item, <I as Iterator>::Item) -> <I as Iterator>::Item,
            >(
                self,
                f: F,
            ) -> Option<<I as Iterator>::Item> {
                iter_reduce(self, f)
            }

            fn min(self) -> Option<<I as Iterator>::Item>
            where
                <I as Iterator>::Item: crate::cmp::Ord,
            {
                iter_min(self)
            }

            fn max(self) -> Option<<I as Iterator>::Item>
            where
                <I as Iterator>::Item: crate::cmp::Ord,
            {
                iter_max(self)
            }

            fn collect<B: super::super::traits::collect::FromIterator<<I as Iterator>::Item>>(
                self,
            ) -> B {
                super::super::traits::collect::FromIterator::from_iter(self)
            }

            fn rev(self) -> Rev<Self>
            where
                Self: DoubleEndedIterator,
            {
                Rev::new(self)
            }

            #[cfg(not(hax_backend_fstar))]
            fn rposition<P: Fn(<I as Iterator>::Item) -> bool>(
                &mut self,
                predicate: P,
            ) -> Option<usize>
            where
                Self: ExactSizeIterator + DoubleEndedIterator,
            {
                iter_rposition(self, predicate)
            }

            fn advance_by(&mut self, n: usize) -> crate::result::Result<(), usize> {
                iter_advance_by(self, n)
            }

            fn cloned<'a, T: Clone + 'a>(self) -> Cloned<Self>
            where
                Self: Iterator<Item = &'a T>,
            {
                Cloned::new(self)
            }

            fn copied<'a, T: Copy + 'a>(self) -> Copied<Self>
            where
                Self: Iterator<Item = &'a T>,
            {
                Copied::new(self)
            }

            fn inspect<F: Fn(&<I as Iterator>::Item)>(self, f: F) -> Inspect<Self, F> {
                Inspect::new(self, f)
            }

            fn filter_map<B, F: Fn(<I as Iterator>::Item) -> Option<B>>(
                self,
                f: F,
            ) -> FilterMap<Self, F> {
                FilterMap::new(self, f)
            }

            fn map_while<B, P: Fn(<I as Iterator>::Item) -> Option<B>>(
                self,
                predicate: P,
            ) -> MapWhile<Self, P> {
                MapWhile::new(self, predicate)
            }

            fn skip_while<P: Fn(&<I as Iterator>::Item) -> bool>(
                self,
                predicate: P,
            ) -> SkipWhile<Self, P> {
                SkipWhile::new(self, predicate)
            }

            fn take_while<P: Fn(&<I as Iterator>::Item) -> bool>(
                self,
                predicate: P,
            ) -> TakeWhile<Self, P> {
                TakeWhile::new(self, predicate)
            }

            #[cfg(not(hax_backend_fstar))]
            fn scan<St, B, F: Fn(&mut St, <I as Iterator>::Item) -> Option<B>>(
                self,
                initial_state: St,
                f: F,
            ) -> super::super::adapters::scan::Scan<Self, St, F> {
                super::super::adapters::scan::Scan::new(self, initial_state, f)
            }

            fn fuse(self) -> Fuse<Self> {
                Fuse::new(self)
            }

            fn cycle(self) -> Cycle<Self>
            where
                Self: Clone,
            {
                Cycle::new(self)
            }

            fn peekable(self) -> Peekable<Self> {
                Peekable::new(self)
            }

            fn intersperse(self, separator: <I as Iterator>::Item) -> Intersperse<Self>
            where
                <I as Iterator>::Item: Clone,
            {
                Intersperse::new(self, separator)
            }

            fn intersperse_with<G: Fn() -> <I as Iterator>::Item>(
                self,
                separator: G,
            ) -> IntersperseWith<Self, G> {
                IntersperseWith::new(self, separator)
            }

            #[hax_lib::requires(N != 0)]
            fn array_chunks<const N: usize>(self) -> ArrayChunks<Self, N> {
                ArrayChunks::new(self)
            }

            #[hax_lib::requires(N != 0)]
            fn map_windows<R, F: Fn(&[<I as Iterator>::Item; N]) -> R, const N: usize>(
                self,
                f: F,
            ) -> MapWindows<Self, F, N> {
                MapWindows::new(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn by_ref(&mut self) -> &mut Self {
                self
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Option::None)
            }

            // Not in the F* model, as on the trait declaration above.
            #[cfg(not(hax_backend_fstar))]
            fn sum<S: Sum<<I as Iterator>::Item>>(self) -> S {
                Sum::sum(self)
            }

            #[cfg(not(hax_backend_fstar))]
            fn product<P: Product<<I as Iterator>::Item>>(self) -> P {
                Product::product(self)
            }

            fn min_by<F: Fn(&<I as Iterator>::Item, &<I as Iterator>::Item) -> Ordering>(
                self,
                compare: F,
            ) -> Option<<I as Iterator>::Item> {
                iter_min_by(self, compare)
            }

            fn max_by<F: Fn(&<I as Iterator>::Item, &<I as Iterator>::Item) -> Ordering>(
                self,
                compare: F,
            ) -> Option<<I as Iterator>::Item> {
                iter_max_by(self, compare)
            }

            #[cfg(not(hax_backend_fstar))]
            fn min_by_key<B: crate::cmp::Ord, F: Fn(&<I as Iterator>::Item) -> B>(
                self,
                f: F,
            ) -> Option<<I as Iterator>::Item> {
                iter_min_by_key(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn max_by_key<B: crate::cmp::Ord, F: Fn(&<I as Iterator>::Item) -> B>(
                self,
                f: F,
            ) -> Option<<I as Iterator>::Item> {
                iter_max_by_key(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn cmp<I2: Iterator<Item = <I as Iterator>::Item>>(self, other: I2) -> Ordering
            where
                <I as Iterator>::Item: crate::cmp::Ord,
            {
                iter_cmp_by(self, other, |x, y| crate::cmp::Ord::cmp(&x, &y))
            }

            fn cmp_by<I2: Iterator, F: Fn(<I as Iterator>::Item, I2::Item) -> Ordering>(
                self,
                other: I2,
                cmp: F,
            ) -> Ordering {
                iter_cmp_by(self, other, cmp)
            }

            #[cfg(not(hax_backend_fstar))]
            fn partial_cmp<I2: Iterator>(self, other: I2) -> Option<Ordering>
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<I2::Item>,
            {
                iter_partial_cmp_by(self, other, |x, y| {
                    crate::cmp::PartialOrd::partial_cmp(&x, &y)
                })
            }

            fn partial_cmp_by<
                I2: Iterator,
                F: Fn(<I as Iterator>::Item, I2::Item) -> Option<Ordering>,
            >(
                self,
                other: I2,
                partial_cmp: F,
            ) -> Option<Ordering> {
                iter_partial_cmp_by(self, other, partial_cmp)
            }

            #[cfg(not(hax_backend_fstar))]
            fn eq<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialEq<I2::Item>,
            {
                iter_eq_by(self, other, |x, y| crate::cmp::PartialEq::eq(&x, &y))
            }

            fn eq_by<I2: Iterator, F: Fn(<I as Iterator>::Item, I2::Item) -> bool>(
                self,
                other: I2,
                eq: F,
            ) -> bool {
                iter_eq_by(self, other, eq)
            }

            #[cfg(not(hax_backend_fstar))]
            fn ne<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialEq<I2::Item>,
            {
                iter_eq_by(self, other, |x, y| crate::cmp::PartialEq::eq(&x, &y)) == false
            }

            #[cfg(not(hax_backend_fstar))]
            fn lt<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<I2::Item>,
            {
                matches!(
                    iter_partial_cmp_by(self, other, |x, y| crate::cmp::PartialOrd::partial_cmp(
                        &x, &y
                    )),
                    Option::Some(Ordering::Less)
                )
            }

            #[cfg(not(hax_backend_fstar))]
            fn le<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<I2::Item>,
            {
                matches!(
                    iter_partial_cmp_by(self, other, |x, y| crate::cmp::PartialOrd::partial_cmp(
                        &x, &y
                    )),
                    Option::Some(Ordering::Less | Ordering::Equal)
                )
            }

            #[cfg(not(hax_backend_fstar))]
            fn gt<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<I2::Item>,
            {
                matches!(
                    iter_partial_cmp_by(self, other, |x, y| crate::cmp::PartialOrd::partial_cmp(
                        &x, &y
                    )),
                    Option::Some(Ordering::Greater)
                )
            }

            #[cfg(not(hax_backend_fstar))]
            fn ge<I2: Iterator>(self, other: I2) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<I2::Item>,
            {
                matches!(
                    iter_partial_cmp_by(self, other, |x, y| crate::cmp::PartialOrd::partial_cmp(
                        &x, &y
                    )),
                    Option::Some(Ordering::Greater | Ordering::Equal)
                )
            }

            #[cfg(not(hax_backend_fstar))]
            fn unzip<A, B, FromA: Default + Extend<A>, FromB: Default + Extend<B>>(
                self,
            ) -> (FromA, FromB)
            where
                Self: Iterator<Item = (A, B)>,
            {
                iter_unzip(self)
            }

            #[cfg(not(hax_backend_fstar))]
            fn partition<
                B: Default + Extend<<I as Iterator>::Item>,
                F: Fn(&<I as Iterator>::Item) -> bool,
            >(
                self,
                f: F,
            ) -> (B, B) {
                iter_partition(self, f)
            }

            fn is_partitioned<P: Fn(<I as Iterator>::Item) -> bool>(self, predicate: P) -> bool {
                iter_is_partitioned(self, predicate)
            }

            #[cfg(not(hax_backend_fstar))]
            fn is_sorted(self) -> bool
            where
                <I as Iterator>::Item: crate::cmp::PartialOrd<<I as Iterator>::Item>,
            {
                // std defers to `is_sorted_by(|a, b| a <= b)`, so incomparable
                // neighbours (a `None` from `partial_cmp`) make the answer `false`.
                iter_is_sorted_by(self, |a, b| {
                    matches!(
                        crate::cmp::PartialOrd::partial_cmp(a, b),
                        Option::Some(Ordering::Less | Ordering::Equal)
                    )
                })
            }

            fn is_sorted_by<F: Fn(&<I as Iterator>::Item, &<I as Iterator>::Item) -> bool>(
                self,
                compare: F,
            ) -> bool {
                iter_is_sorted_by(self, compare)
            }

            #[cfg(not(hax_backend_fstar))]
            fn is_sorted_by_key<K: crate::cmp::PartialOrd<K>, F: Fn(<I as Iterator>::Item) -> K>(
                self,
                f: F,
            ) -> bool {
                iter_is_sorted_by(Map::new(self, f), |a, b| {
                    matches!(
                        crate::cmp::PartialOrd::partial_cmp(a, b),
                        Option::Some(Ordering::Less | Ordering::Equal)
                    )
                })
            }

            #[cfg(not(hax_backend_fstar))]
            fn collect_into<E: Extend<<I as Iterator>::Item>>(self, collection: &mut E) -> &mut E {
                collection.extend(self);
                collection
            }

            #[cfg(not(hax_backend_fstar))]
            fn next_chunk<const N: usize>(
                &mut self,
            ) -> Result<
                [<I as Iterator>::Item; N],
                crate::array::iter::IntoIter<<I as Iterator>::Item, N>,
            >
            where
                <I as Iterator>::Item: Clone,
            {
                iter_next_chunk(self)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_fold<
                B,
                R: Try<Output = B> + FromResidual<<R as Try>::Residual>,
                F: Fn(B, <I as Iterator>::Item) -> R,
            >(
                &mut self,
                init: B,
                f: F,
            ) -> R {
                iter_try_fold(self, init, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_for_each<
                R: Try<Output = ()> + FromResidual<<R as Try>::Residual>,
                F: Fn(<I as Iterator>::Item) -> R,
            >(
                &mut self,
                f: F,
            ) -> R {
                iter_try_for_each(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_find<R, F: Fn(&<I as Iterator>::Item) -> R>(
                &mut self,
                f: F,
            ) -> <<R as Try>::Residual as Residual<Option<<I as Iterator>::Item>>>::TryType
            where
                R: Try<Output = bool>,
                <R as Try>::Residual: Residual<Option<<I as Iterator>::Item>>,
                <<R as Try>::Residual as Residual<Option<<I as Iterator>::Item>>>::TryType:
                    FromResidual<<R as Try>::Residual>,
            {
                iter_try_find(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_reduce<R, F: Fn(<I as Iterator>::Item, <I as Iterator>::Item) -> R>(
                &mut self,
                f: F,
            ) -> <<R as Try>::Residual as Residual<Option<<I as Iterator>::Item>>>::TryType
            where
                R: Try<Output = <I as Iterator>::Item>,
                <R as Try>::Residual: Residual<Option<<I as Iterator>::Item>>,
                <<R as Try>::Residual as Residual<Option<<I as Iterator>::Item>>>::TryType:
                    FromResidual<<R as Try>::Residual>,
            {
                iter_try_reduce(self, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_collect<B>(
                &mut self,
            ) -> <<<I as Iterator>::Item as Try>::Residual as Residual<B>>::TryType
            where
                <I as Iterator>::Item: Try,
                <<I as Iterator>::Item as Try>::Residual: Residual<B>,
                B: super::collect::FromIterator<<<I as Iterator>::Item as Try>::Output>,
                <<<I as Iterator>::Item as Try>::Residual as Residual<B>>::TryType:
                    FromResidual<<<I as Iterator>::Item as Try>::Residual>,
            {
                iter_try_collect(self)
            }
        }

        #[hax_lib::attributes]
        impl<I: Iterator> super::collect::IntoIterator for I {
            type Item = I::Item;
            type IntoIter = Self;
            fn into_iter(self) -> Self {
                self
            }
        }
    }
    pub mod accum {
        use super::iterator::Iterator;
        use crate::option::Option;

        // No `#[hax_lib::attributes]` on these two: the macro reorders the
        // generics and rustc then rejects the defaulted `A = Self` as
        // non-trailing.
        /// See [`std::iter::Sum`]
        pub trait Sum<A = Self>: Sized {
            /// See [`std::iter::Sum::sum`]
            fn sum<I: Iterator<Item = A>>(iter: I) -> Self;
        }

        /// See [`std::iter::Product`]
        pub trait Product<A = Self>: Sized {
            /// See [`std::iter::Product::product`]
            fn product<I: Iterator<Item = A>>(iter: I) -> Self;
        }

        // `+` / `*` on the primitive, as std does, so that the overflow
        // obligation is the same one the rest of this model raises.
        macro_rules! sum_product_int {
            ($($t:ty)*) => { $(
                // opaque: while-let loop is not supported by hax FunctionalizeLoops
                #[hax_lib::opaque]
                impl Sum<$t> for $t {
                    fn sum<I: Iterator<Item = $t>>(mut iter: I) -> $t {
                        let mut acc: $t = 0;
                        while let Option::Some(x) = iter.next() {
                            acc = acc + x;
                        }
                        acc
                    }
                }
                // opaque: while-let loop is not supported by hax FunctionalizeLoops
                #[hax_lib::opaque]
                impl Product<$t> for $t {
                    fn product<I: Iterator<Item = $t>>(mut iter: I) -> $t {
                        let mut acc: $t = 1;
                        while let Option::Some(x) = iter.next() {
                            acc = acc * x;
                        }
                        acc
                    }
                }
            )* }
        }

        sum_product_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);
    }
    pub mod double_ended {
        use super::iterator::Iterator;
        use crate::option::Option;
        use crate::result::Result;

        /// See [`std::iter::DoubleEndedIterator`]
        #[hax_lib::attributes]
        pub trait DoubleEndedIterator: Iterator {
            /// See [`std::iter::DoubleEndedIterator::next_back`]
            #[hax_lib::requires(true)]
            fn next_back(&mut self) -> Option<Self::Item>;
        }

        // Companion trait for `DoubleEndedIterator`'s default methods, for the
        // reason given at the top of this file (see also `IteratorMethods`).
        #[hax_lib::attributes]
        pub(crate) trait DoubleEndedIteratorMethods: DoubleEndedIterator {
            /// The residual count is a plain `usize` (always non-zero on `Err`)
            /// because the model has no `core::num::NonZero`.
            fn advance_back_by(&mut self, n: usize) -> Result<(), usize>;
            fn nth_back(&mut self, n: usize) -> Option<Self::Item>;
            fn rfind<P: Fn(&Self::Item) -> bool>(&mut self, predicate: P) -> Option<Self::Item>;
            fn rfold<B, F: Fn(B, Self::Item) -> B>(self, init: B, f: F) -> B;
            /// `R: FromResidual<R::Residual>` is a deviation: std gets it from
            /// `Try`'s supertrait, which the model's `ops::try_trait::Try` lacks.
            #[cfg(not(hax_backend_fstar))]
            fn try_rfold<
                B,
                R: crate::ops::try_trait::Try<Output = B>
                    + crate::ops::try_trait::FromResidual<<R as crate::ops::try_trait::Try>::Residual>,
                F: Fn(B, Self::Item) -> R,
            >(
                &mut self,
                init: B,
                f: F,
            ) -> R;
        }

        // opaque: while-loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_advance_back_by<I: DoubleEndedIterator>(
            iter: &mut I,
            n: usize,
        ) -> Result<(), usize> {
            let mut remaining = n;
            while remaining > 0 {
                match iter.next_back() {
                    Option::None => return Result::Err(remaining),
                    Option::Some(_) => remaining -= 1,
                }
            }
            Result::Ok(())
        }

        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_nth_back<I: DoubleEndedIterator>(iter: &mut I, n: usize) -> Option<I::Item> {
            let mut remaining = n;
            loop {
                match iter.next_back() {
                    Option::None => return Option::None,
                    Option::Some(v) => {
                        if remaining == 0 {
                            return Option::Some(v);
                        }
                        remaining -= 1;
                    }
                }
            }
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_rfind<I: DoubleEndedIterator, P: Fn(&I::Item) -> bool>(
            iter: &mut I,
            predicate: P,
        ) -> Option<I::Item> {
            while let Option::Some(x) = iter.next_back() {
                if predicate(&x) {
                    return Option::Some(x);
                }
            }
            Option::None
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_rfold<I: DoubleEndedIterator, B, F: Fn(B, I::Item) -> B>(
            mut iter: I,
            init: B,
            f: F,
        ) -> B {
            let mut accum = init;
            while let Option::Some(x) = iter.next_back() {
                accum = f(accum, x);
            }
            accum
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        fn iter_try_rfold<
            I: DoubleEndedIterator,
            B,
            R: crate::ops::try_trait::Try<Output = B>
                + crate::ops::try_trait::FromResidual<<R as crate::ops::try_trait::Try>::Residual>,
            F: Fn(B, <I as Iterator>::Item) -> R,
        >(
            iter: &mut I,
            init: B,
            f: F,
        ) -> R {
            use crate::ops::control_flow::ControlFlow;
            use crate::ops::try_trait::{FromResidual, Try};
            let mut accum = init;
            while let Option::Some(x) = iter.next_back() {
                match Try::branch(f(accum, x)) {
                    ControlFlow::Continue(v) => accum = v,
                    ControlFlow::Break(residual) => return FromResidual::from_residual(residual),
                }
            }
            Try::from_output(accum)
        }

        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        // `<I as Iterator>::Item` rather than `Self::Item`: `Item` reaches this
        // impl through `DoubleEndedIterator`'s supertrait, which hax cannot
        // qualify on its own (cryspen/hax#2089).
        impl<I: DoubleEndedIterator> DoubleEndedIteratorMethods for I {
            fn advance_back_by(&mut self, n: usize) -> Result<(), usize> {
                iter_advance_back_by(self, n)
            }

            fn nth_back(&mut self, n: usize) -> Option<<I as Iterator>::Item> {
                iter_nth_back(self, n)
            }

            fn rfind<P: Fn(&<I as Iterator>::Item) -> bool>(
                &mut self,
                predicate: P,
            ) -> Option<<I as Iterator>::Item> {
                iter_rfind(self, predicate)
            }

            fn rfold<B, F: Fn(B, <I as Iterator>::Item) -> B>(self, init: B, f: F) -> B {
                iter_rfold(self, init, f)
            }

            #[cfg(not(hax_backend_fstar))]
            fn try_rfold<
                B,
                R: crate::ops::try_trait::Try<Output = B>
                    + crate::ops::try_trait::FromResidual<<R as crate::ops::try_trait::Try>::Residual>,
                F: Fn(B, <I as Iterator>::Item) -> R,
            >(
                &mut self,
                init: B,
                f: F,
            ) -> R {
                iter_try_rfold(self, init, f)
            }
        }
    }
    pub mod exact_size {
        use super::iterator::Iterator;

        /// See [`std::iter::ExactSizeIterator`]
        #[hax_lib::attributes]
        pub trait ExactSizeIterator: Iterator {
            /// See [`std::iter::ExactSizeIterator::len`]
            // `len` is a required method here: std derives it from `size_hint`,
            // which the model's `Iterator` does not have.
            #[hax_lib::requires(true)]
            fn len(&self) -> usize;
        }

        // Companion trait for the one default method, as for `IteratorMethods`.
        // Out of F*: hax derives a trait method's contract lemmas as top-level
        // `f_<method>_pre`/`_post` and puts a whole crate's traits in one bundle
        // module, so a method name is effectively crate-global there. This
        // `is_empty` collides with `ops::range::RangeBoundsDefaults::is_empty`,
        // which the F* library needs — keep `ExactSizeIteratorMethods` out of F*.
        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::attributes]
        pub(crate) trait ExactSizeIteratorMethods: ExactSizeIterator {
            fn is_empty(&self) -> bool;
        }

        #[cfg(not(hax_backend_fstar))]
        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        impl<I: ExactSizeIterator> ExactSizeIteratorMethods for I {
            fn is_empty(&self) -> bool {
                self.len() == 0
            }
        }
    }
    pub mod marker {
        /// See [`std::iter::FusedIterator`]
        // std marks this `unsafe trait`; the model drops the `unsafe` because it
        // has no unsafety obligation to express and hax does not model one.
        pub trait FusedIterator: super::iterator::Iterator {}
        /// See [`std::iter::TrustedLen`]
        // `unsafe` dropped, as for `FusedIterator`.
        pub trait TrustedLen: super::iterator::Iterator {}
        /// See [`std::iter::TrustedStep`]
        // `unsafe` dropped, as above. Excluded from the F* extraction because
        // its supertrait `Step` is (`CORE_MODELS_FSTAR_EXCLUDES` drops all of
        // `core_models::iter::range`), which would leave a dangling reference.
        #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
        pub trait TrustedStep: super::super::range::Step {}
    }
    pub mod collect {
        /// See [`std::iter::IntoIterator`]
        pub trait IntoIterator {
            // The trait bound `IntoIter: Iterator<Item = Self::Item>` is
            // omitted to avoid coinduction; the `Item` associated type
            // itself is kept so downstream Aeneas extractions (which see
            // std's IntoIterator with 2 associated types) produce
            // 3-argument references that match our extracted struct.
            type Item;
            type IntoIter;
            fn into_iter(self) -> Self::IntoIter;
        }
        /// See [`std::iter::FromIterator`]
        #[hax_lib::attributes]
        pub trait FromIterator<A>: Sized {
            #[hax_lib::requires(true)]
            fn from_iter<T: IntoIterator>(iter: T) -> Self;
        }
        /// See [`std::iter::Extend`]
        #[hax_lib::attributes]
        pub trait Extend<A> {
            /// See [`std::iter::Extend::extend`]
            // The `IntoIter: Iterator` bound that `IntoIterator` above
            // deliberately omits is spelled out here, so that implementors can
            // actually walk `iter`.
            #[hax_lib::requires(true)]
            fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T)
            where
                T::IntoIter: super::iterator::Iterator<Item = A>;
        }

        // Companion trait for `Extend`'s default methods, for the reason given at
        // the top of this file (see also `IteratorMethods`).
        #[hax_lib::attributes]
        pub(crate) trait ExtendMethods<A>: Extend<A> {
            fn extend_one(&mut self, item: A);
            fn extend_reserve(&mut self, additional: usize);
        }

        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        // opaque for F*: `extend_one` feeds `extend` a `Once<A>`, and F* cannot
        // reduce that iterator's `Item` to `A` while its instance is still an
        // unresolved `solve`.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A, E: Extend<A>> ExtendMethods<A> for E {
            fn extend_one(&mut self, item: A) {
                self.extend(super::super::sources::once::once(item))
            }

            // std's default is a no-op: reserving is an optimisation, and the
            // model has no capacity to reserve.
            fn extend_reserve(&mut self, additional: usize) {}
        }
    }
}

pub mod adapters {
    pub mod enumerate {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Enumerate`]
        pub struct Enumerate<I> {
            iter: I,
            count: usize,
        }
        #[hax_lib::attributes]
        impl<I> Enumerate<I> {
            pub fn new(iter: I) -> Enumerate<I> {
                Enumerate { iter, count: 0 }
            }
            /// See [`std::iter::Enumerate::next_index`]
            pub fn next_index(&self) -> usize {
                self.count
            }
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Iterator for Enumerate<I> {
            type Item = (usize, <I as Iterator>::Item);

            fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
                match self.iter.next() {
                    Option::Some(a) => {
                        let i = self.count;
                        // TODO check what to do here. It would be bad to have an iterator with
                        // more than usize::MAX elements, this could be a requirement (but hard to formulate).
                        // F* only: the Lean library has no `hax_lib::assume` model.
                        #[cfg(hax_backend_fstar)]
                        hax_lib::assume!(self.count < crate::num::usize::MAX);
                        self.count += 1;
                        Option::Some((i, a))
                    }
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        impl<I: super::super::traits::exact_size::ExactSizeIterator>
            super::super::traits::exact_size::ExactSizeIterator for Enumerate<I>
        {
            fn len(&self) -> usize {
                super::super::traits::exact_size::ExactSizeIterator::len(&self.iter)
            }
        }
    }
    pub mod step_by {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::StepBy`]
        pub struct StepBy<I> {
            iter: I,
            step: usize,
        }

        #[hax_lib::attributes]
        impl<I> StepBy<I> {
            // std panics in `Iterator::step_by`, which is this constructor's only caller.
            #[hax_lib::requires(step > 0)]
            pub fn new(iter: I, step: usize) -> Self {
                if step == 0 {
                    crate::panicking::internal::panic()
                }
                StepBy { iter, step }
            }
        }

        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator> Iterator for StepBy<I> {
            type Item = <I as Iterator>::Item;

            // Yields indices 0, step, 2*step, …, so the first call must not skip.
            fn next(&mut self) -> Option<<I as Iterator>::Item> {
                let current = self.iter.next();
                // No early exit: Aeneas can't translate `break`, and `next` on an
                // exhausted iterator is a no-op.
                for _ in 1..self.step {
                    self.iter.next();
                }
                current
            }
        }
    }
    pub mod map {
        /// See [`std::iter::Map`]
        pub struct Map<I, F> {
            iter: I,
            f: F,
        }

        #[hax_lib::attributes]
        impl<I, F> Map<I, F> {
            pub fn new(iter: I, f: F) -> Self {
                Self { iter, f }
            }
        }
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, O, F: Fn(I::Item) -> O> Iterator for Map<I, F> {
            type Item = O;

            fn next(&mut self) -> Option<O> {
                match self.iter.next() {
                    Option::Some(v) => Option::Some((self.f)(v)),
                    Option::None => Option::None,
                }
            }
        }

        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: DoubleEndedIterator, O, F: Fn(I::Item) -> O> DoubleEndedIterator for Map<I, F> {
            fn next_back(&mut self) -> Option<O> {
                match self.iter.next_back() {
                    Option::Some(v) => Option::Some((self.f)(v)),
                    Option::None => Option::None,
                }
            }
        }

        #[hax_lib::attributes]
        // opaque for F*: building this record needs the `Iterator` instance for the
        // adapter, which F* cannot rederive from an `ExactSizeIterator` bound plus
        // the adapter's extra `Fn`/`Clone` argument.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: ExactSizeIterator, O, F: Fn(I::Item) -> O> ExactSizeIterator for Map<I, F> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(&self.iter)
            }
        }
    }
    pub mod take {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Take`]
        pub struct Take<I> {
            iter: I,
            n: usize,
        }
        #[hax_lib::attributes]
        impl<I> Take<I> {
            pub fn new(iter: I, n: usize) -> Take<I> {
                Take { iter, n }
            }
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Iterator for Take<I> {
            type Item = <I as Iterator>::Item;

            fn next(&mut self) -> Option<<I as Iterator>::Item> {
                if self.n != 0 {
                    self.n -= 1;
                    self.iter.next()
                } else {
                    Option::None
                }
            }
        }
    }
    pub mod flat_map {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::FlatMap`]
        pub struct FlatMap<I, U, F> {
            it: I,
            f: F,
            current: Option<U>,
        }
        #[hax_lib::attributes]
        impl<I: Iterator, U: Iterator, F: Fn(I::Item) -> U> FlatMap<I, U, F> {
            pub fn new(it: I, f: F) -> Self {
                Self {
                    it,
                    f,
                    current: Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, U: Iterator, F: Fn(I::Item) -> U> Iterator for FlatMap<I, U, F> {
            type Item = U::Item;
            fn next(&mut self) -> Option<U::Item> {
                loop {
                    if let Option::Some(current_it) = &mut self.current
                        && let Option::Some(v) = current_it.next()
                    {
                        return Option::Some(v);
                    } else {
                        match self.it.next() {
                            Option::Some(c) => self.current = Option::Some((self.f)(c)),
                            Option::None => return Option::None,
                        }
                    }
                }
            }
        }
    }
    pub mod flatten {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Flatten`]
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct Flatten<I: Iterator>
        where
            I::Item: Iterator,
        {
            it: I,
            current: Option<I::Item>,
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Flatten<I>
        where
            I::Item: Iterator,
        {
            pub fn new(it: I) -> Self {
                Self {
                    it,
                    current: Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator> Iterator for Flatten<I>
        where
            I::Item: Iterator,
        {
            type Item = <<I as Iterator>::Item as Iterator>::Item;
            fn next(&mut self) -> Option<<<I as Iterator>::Item as Iterator>::Item> {
                loop {
                    if let Option::Some(current_it) = &mut self.current
                        && let Option::Some(v) = current_it.next()
                    {
                        return Option::Some(v);
                    } else {
                        match self.it.next() {
                            Option::Some(c) => self.current = Option::Some(c),
                            Option::None => return Option::None,
                        }
                    }
                }
            }
        }
    }
    pub mod zip {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Zip`]
        pub struct Zip<I1, I2> {
            it1: I1,
            it2: I2,
        }
        #[hax_lib::attributes]
        impl<I1: Iterator, I2: Iterator> Zip<I1, I2> {
            pub fn new(it1: I1, it2: I2) -> Self {
                Self { it1, it2 }
            }
        }
        /// See [`std::iter::zip`]
        // Takes `Iterator`s rather than std's `IntoIterator`s, matching
        // `IteratorMethods::zip`: the model's `IntoIterator` deliberately does
        // not bound `IntoIter: Iterator` (no coinduction).
        pub fn zip<A: Iterator, B: Iterator>(a: A, b: B) -> Zip<A, B> {
            Zip::new(a, b)
        }
        #[hax_lib::attributes]
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I1: Iterator, I2: Iterator> Iterator for Zip<I1, I2> {
            type Item = (I1::Item, I2::Item);
            fn next(&mut self) -> Option<Self::Item> {
                match self.it1.next() {
                    Option::Some(v1) => match self.it2.next() {
                        Option::Some(v2) => Option::Some((v1, v2)),
                        Option::None => Option::None,
                    },
                    Option::None => Option::None,
                }
            }
        }
    }
    pub mod filter {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Filter`]
        pub struct Filter<I, P> {
            iter: I,
            predicate: P,
        }
        #[hax_lib::attributes]
        impl<I, P> Filter<I, P> {
            pub fn new(iter: I, predicate: P) -> Self {
                Self { iter, predicate }
            }
        }
        #[hax_lib::attributes]
        // opaque: loop + Fn output projection not provably bool in F*
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[cfg_attr(charon, hax_lib::exclude)]
        impl<I: Iterator, P: Fn(&I::Item) -> bool> Iterator for Filter<I, P> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                loop {
                    match self.iter.next() {
                        Option::Some(v) => {
                            if (self.predicate)(&v) {
                                return Option::Some(v);
                            }
                        }
                        Option::None => return Option::None,
                    }
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for the same reason as the `Iterator` impl above.
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)]
        impl<I: super::super::traits::double_ended::DoubleEndedIterator, P: Fn(&I::Item) -> bool>
            super::super::traits::double_ended::DoubleEndedIterator for Filter<I, P>
        {
            fn next_back(&mut self) -> Option<I::Item> {
                loop {
                    match self.iter.next_back() {
                        Option::Some(v) => {
                            if (self.predicate)(&v) {
                                return Option::Some(v);
                            }
                        }
                        Option::None => return Option::None,
                    }
                }
            }
        }
    }
    pub mod chain {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Chain`]
        pub struct Chain<A, B> {
            a: Option<A>,
            b: B,
        }
        #[hax_lib::attributes]
        impl<A: Iterator, B: Iterator<Item = A::Item>> Chain<A, B> {
            pub fn new(a: A, b: B) -> Self {
                Self {
                    a: Option::Some(a),
                    b,
                }
            }
        }
        /// See [`std::iter::chain`]
        // Takes `Iterator`s rather than std's `IntoIterator`s, for the reason
        // given on `zip`.
        pub fn chain<A: Iterator, B: Iterator<Item = A::Item>>(a: A, b: B) -> Chain<A, B> {
            Chain::new(a, b)
        }
        #[hax_lib::attributes]
        // opaque: `ref mut` pattern in if-let is not supported by hax
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A: Iterator, B: Iterator<Item = A::Item>> Iterator for Chain<A, B> {
            type Item = A::Item;
            fn next(&mut self) -> Option<A::Item> {
                if let Option::Some(ref mut a) = self.a {
                    match a.next() {
                        Option::Some(v) => return Option::Some(v),
                        Option::None => self.a = Option::None,
                    }
                }
                self.b.next()
            }
        }
        #[hax_lib::attributes]
        // opaque: `ref mut` pattern in if-let is not supported by hax
        #[hax_lib::opaque]
        impl<
            A: super::super::traits::double_ended::DoubleEndedIterator,
            B: super::super::traits::double_ended::DoubleEndedIterator<Item = A::Item>,
        > super::super::traits::double_ended::DoubleEndedIterator for Chain<A, B>
        {
            fn next_back(&mut self) -> Option<A::Item> {
                match self.b.next_back() {
                    Option::Some(v) => Option::Some(v),
                    Option::None => {
                        if let Option::Some(ref mut a) = self.a {
                            a.next_back()
                        } else {
                            Option::None
                        }
                    }
                }
            }
        }
    }
    pub mod skip {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Skip`]
        pub struct Skip<I> {
            iter: I,
            n: usize,
        }
        #[hax_lib::attributes]
        impl<I> Skip<I> {
            pub fn new(iter: I, n: usize) -> Self {
                Self { iter, n }
            }
        }
        #[hax_lib::attributes]
        // opaque: while-loop generates Rust_primitives.Hax.while_loop, causing F* dependency cycle
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator> Iterator for Skip<I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                while self.n > 0 {
                    self.n -= 1;
                    if let Option::None = self.iter.next() {
                        return Option::None;
                    }
                }
                self.iter.next()
            }
        }
    }
    pub mod rev {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Rev`]
        pub struct Rev<I> {
            iter: I,
        }
        #[hax_lib::attributes]
        impl<I> Rev<I> {
            pub fn new(it: I) -> Rev<I> {
                Rev { iter: it }
            }
            /// See [`std::iter::Rev::into_inner`]
            pub fn into_inner(self) -> I {
                self.iter
            }
        }
        #[hax_lib::attributes]
        impl<I: DoubleEndedIterator> Iterator for Rev<I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                self.iter.next_back()
            }
        }
        #[hax_lib::attributes]
        impl<I: DoubleEndedIterator> DoubleEndedIterator for Rev<I> {
            fn next_back(&mut self) -> Option<I::Item> {
                self.iter.next()
            }
        }
        #[hax_lib::attributes]
        impl<I: DoubleEndedIterator + ExactSizeIterator> ExactSizeIterator for Rev<I> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(&self.iter)
            }
        }
    }
    pub mod cloned {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Cloned`]
        // The `Clone` bound is Rust's own (`&self -> Self`) rather than the
        // model's consuming `crate::clone::Clone`, which cannot produce a `T`
        // from a `&T`.
        pub struct Cloned<I> {
            it: I,
        }
        #[hax_lib::attributes]
        impl<I> Cloned<I> {
            pub fn new(it: I) -> Self {
                Self { it }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: the `Item = &'a T` equality from the impl's bound is not
        // carried into the body, so F* sees the `Option<I::Item>` the inner
        // iterator returns as unrelated to `Option<T>`. Same escape hatch as the
        // `Map` adapter above.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Clone + 'a, I: Iterator<Item = &'a T>> Iterator for Cloned<I> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                match self.it.next() {
                    Option::Some(v) => Option::Some(v.clone()),
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: the `Item = &'a T` equality from the impl's bound is not
        // carried into the body, so F* sees the `Option<I::Item>` the inner
        // iterator returns as unrelated to `Option<T>`. Same escape hatch as the
        // `Map` adapter above.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Clone + 'a, I: DoubleEndedIterator<Item = &'a T>> DoubleEndedIterator for Cloned<I> {
            fn next_back(&mut self) -> Option<T> {
                match self.it.next_back() {
                    Option::Some(v) => Option::Some(v.clone()),
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: building this record needs the `Iterator` instance for
        // `Cloned`/`Copied`, which F* cannot rederive from an `ExactSizeIterator`
        // bound because of the `Item = &'a T` equality.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Clone + 'a, I: ExactSizeIterator<Item = &'a T>> ExactSizeIterator for Cloned<I> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(&self.it)
            }
        }
    }
    pub mod copied {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Copied`]
        // `Copy` is Rust's own, as std's is: the model's `marker::Copy` carries
        // no dereference operation.
        pub struct Copied<I> {
            it: I,
        }
        #[hax_lib::attributes]
        impl<I> Copied<I> {
            pub fn new(it: I) -> Self {
                Self { it }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: the `Item = &'a T` equality from the impl's bound is not
        // carried into the body, so F* sees the `Option<I::Item>` the inner
        // iterator returns as unrelated to `Option<T>`. Same escape hatch as the
        // `Map` adapter above.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Copy + 'a, I: Iterator<Item = &'a T>> Iterator for Copied<I> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                match self.it.next() {
                    Option::Some(v) => Option::Some(*v),
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: the `Item = &'a T` equality from the impl's bound is not
        // carried into the body, so F* sees the `Option<I::Item>` the inner
        // iterator returns as unrelated to `Option<T>`. Same escape hatch as the
        // `Map` adapter above.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Copy + 'a, I: DoubleEndedIterator<Item = &'a T>> DoubleEndedIterator for Copied<I> {
            fn next_back(&mut self) -> Option<T> {
                match self.it.next_back() {
                    Option::Some(v) => Option::Some(*v),
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: building this record needs the `Iterator` instance for
        // `Cloned`/`Copied`, which F* cannot rederive from an `ExactSizeIterator`
        // bound because of the `Item = &'a T` equality.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<'a, T: Copy + 'a, I: ExactSizeIterator<Item = &'a T>> ExactSizeIterator for Copied<I> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(&self.it)
            }
        }
    }
    pub mod inspect {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Inspect`]
        pub struct Inspect<I, F> {
            it: I,
            f: F,
        }
        #[hax_lib::attributes]
        impl<I, F> Inspect<I, F> {
            pub fn new(it: I, f: F) -> Self {
                Self { it, f }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: as for the `Map` and `Filter` adapters, F* cannot see
        // that the closure's output type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, F: Fn(&I::Item)> Iterator for Inspect<I, F> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                match self.it.next() {
                    Option::Some(v) => {
                        (self.f)(&v);
                        Option::Some(v)
                    }
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: as for the `Map` and `Filter` adapters, F* cannot see
        // that the closure's output type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: DoubleEndedIterator, F: Fn(&I::Item)> DoubleEndedIterator for Inspect<I, F> {
            fn next_back(&mut self) -> Option<I::Item> {
                match self.it.next_back() {
                    Option::Some(v) => {
                        (self.f)(&v);
                        Option::Some(v)
                    }
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: building this record needs the `Iterator` instance for the
        // adapter, which F* cannot rederive from an `ExactSizeIterator` bound plus
        // the adapter's extra `Fn`/`Clone` argument.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: ExactSizeIterator, F: Fn(&I::Item)> ExactSizeIterator for Inspect<I, F> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(&self.it)
            }
        }
    }
    pub mod filter_map {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::FilterMap`]
        pub struct FilterMap<I, F> {
            it: I,
            f: F,
        }
        #[hax_lib::attributes]
        impl<I, F> FilterMap<I, F> {
            pub fn new(it: I, f: F) -> Self {
                Self { it, f }
            }
        }
        #[hax_lib::attributes]
        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        impl<I: Iterator, B, F: Fn(I::Item) -> Option<B>> Iterator for FilterMap<I, F> {
            type Item = B;
            fn next(&mut self) -> Option<B> {
                loop {
                    match self.it.next() {
                        Option::Some(v) => {
                            if let Option::Some(b) = (self.f)(v) {
                                return Option::Some(b);
                            }
                        }
                        Option::None => return Option::None,
                    }
                }
            }
        }
    }
    pub mod map_while {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::MapWhile`]
        pub struct MapWhile<I, P> {
            it: I,
            predicate: P,
        }
        #[hax_lib::attributes]
        impl<I, P> MapWhile<I, P> {
            pub fn new(it: I, predicate: P) -> Self {
                Self { it, predicate }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: as for the `Map` and `Filter` adapters, F* cannot see
        // that the closure's output type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, B, P: Fn(I::Item) -> Option<B>> Iterator for MapWhile<I, P> {
            type Item = B;
            fn next(&mut self) -> Option<B> {
                match self.it.next() {
                    Option::Some(v) => (self.predicate)(v),
                    Option::None => Option::None,
                }
            }
        }
    }
    pub mod skip_while {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::SkipWhile`]
        pub struct SkipWhile<I, P> {
            it: I,
            // `true` once the predicate has failed, after which nothing is skipped.
            done_skipping: bool,
            predicate: P,
        }
        #[hax_lib::attributes]
        impl<I, P> SkipWhile<I, P> {
            pub fn new(it: I, predicate: P) -> Self {
                Self {
                    it,
                    done_skipping: false,
                    predicate,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque: loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        impl<I: Iterator, P: Fn(&I::Item) -> bool> Iterator for SkipWhile<I, P> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                loop {
                    match self.it.next() {
                        Option::Some(v) => {
                            if self.done_skipping {
                                return Option::Some(v);
                            }
                            if (self.predicate)(&v) == false {
                                self.done_skipping = true;
                                return Option::Some(v);
                            }
                        }
                        Option::None => return Option::None,
                    }
                }
            }
        }
    }
    pub mod take_while {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::TakeWhile`]
        pub struct TakeWhile<I, P> {
            it: I,
            // `true` once the predicate has failed; the adapter then stays empty.
            // Named `exhausted`, not `done`: Lean opens the enclosing
            // namespaces of a declaration, so a field `done` shadows the
            // ControlFlow constructor that Aeneas's loop translation emits
            // inside this struct's own namespace.
            exhausted: bool,
            predicate: P,
        }
        #[hax_lib::attributes]
        impl<I, P> TakeWhile<I, P> {
            pub fn new(it: I, predicate: P) -> Self {
                Self {
                    it,
                    exhausted: false,
                    predicate,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: as for the `Map` and `Filter` adapters, F* cannot see
        // that the closure's output type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, P: Fn(&I::Item) -> bool> Iterator for TakeWhile<I, P> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                if self.exhausted {
                    Option::None
                } else {
                    match self.it.next() {
                        Option::Some(v) => {
                            if (self.predicate)(&v) {
                                Option::Some(v)
                            } else {
                                self.exhausted = true;
                                Option::None
                            }
                        }
                        Option::None => {
                            self.exhausted = true;
                            Option::None
                        }
                    }
                }
            }
        }
    }
    // Not part of the F* model: the `Fn(&mut St, _)` bound its `Iterator` impl
    // needs is rejected by hax (HAX0003 `DirectAndMut`, hacspec/hax#420).
    #[cfg(not(hax_backend_fstar))]
    pub mod scan {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Scan`]
        pub struct Scan<I, St, F> {
            iter: I,
            state: St,
            f: F,
        }
        #[hax_lib::attributes]
        impl<I, St, F> Scan<I, St, F> {
            pub fn new(it: I, state: St, f: F) -> Self {
                Self { iter: it, state, f }
            }
        }
        #[hax_lib::attributes]
        // Out of the Lean extraction for the same reason it is out of the F* one:
        // the model's `Fn` has no way to hand a mutated `&mut St` back, so
        // Aeneas's translation of the call does not typecheck.
        #[cfg_attr(charon, aeneas::exclude)]
        impl<I: Iterator, St, B, F: Fn(&mut St, I::Item) -> Option<B>> Iterator for Scan<I, St, F> {
            type Item = B;
            fn next(&mut self) -> Option<B> {
                match self.iter.next() {
                    Option::Some(v) => (self.f)(&mut self.state, v),
                    Option::None => Option::None,
                }
            }
        }
    }
    pub mod fuse {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::iterator::Iterator;
        use super::super::traits::marker::FusedIterator;
        use crate::option::Option;
        /// See [`std::iter::Fuse`]
        // std stores `Option<I>` and drops the iterator once it is done; a `bool`
        // is enough to give the same answers and avoids moving out of `&mut self`.
        pub struct Fuse<I> {
            iter: I,
            // Named `exhausted`, not `done`: Lean opens the enclosing
            // namespaces of a declaration, so a field `done` shadows the
            // ControlFlow constructor that Aeneas's loop translation emits
            // inside this struct's own namespace.
            exhausted: bool,
        }
        #[hax_lib::attributes]
        impl<I> Fuse<I> {
            pub fn new(it: I) -> Self {
                Self {
                    iter: it,
                    exhausted: false,
                }
            }
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Iterator for Fuse<I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                if self.exhausted {
                    Option::None
                } else {
                    match self.iter.next() {
                        Option::Some(v) => Option::Some(v),
                        Option::None => {
                            self.exhausted = true;
                            Option::None
                        }
                    }
                }
            }
        }
        #[hax_lib::attributes]
        impl<I: DoubleEndedIterator> DoubleEndedIterator for Fuse<I> {
            fn next_back(&mut self) -> Option<I::Item> {
                if self.exhausted {
                    Option::None
                } else {
                    match self.iter.next_back() {
                        Option::Some(v) => Option::Some(v),
                        Option::None => {
                            self.exhausted = true;
                            Option::None
                        }
                    }
                }
            }
        }
        impl<I: Iterator> FusedIterator for Fuse<I> {}
    }
    pub mod cycle {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::Cycle`]
        // `Clone` is Rust's own: restarting means copying the original iterator
        // while keeping it, which the model's consuming `Clone` cannot do.
        pub struct Cycle<I> {
            orig: I,
            iter: I,
        }
        #[hax_lib::attributes]
        impl<I: Clone> Cycle<I> {
            pub fn new(it: I) -> Self {
                Self {
                    orig: it.clone(),
                    iter: it,
                }
            }
        }
        #[hax_lib::attributes]
        impl<I: Iterator + Clone> Iterator for Cycle<I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                match self.iter.next() {
                    Option::Some(v) => Option::Some(v),
                    Option::None => {
                        // An empty original stays empty, as in std.
                        self.iter = self.orig.clone();
                        self.iter.next()
                    }
                }
            }
        }
    }
    pub mod peekable {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use crate::result::Result;
        use rust_primitives::sequence::{Seq, seq_empty, seq_index, seq_len, seq_push, seq_remove};
        /// See [`std::iter::Peekable`]
        // The look-ahead lives in a `Seq` of length at most one rather than in an
        // `Option<Option<I::Item>>`, so that `next` can move it out (the model has
        // neither `mem::replace` nor `Option::take` available to it).
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct Peekable<I: Iterator> {
            iter: I,
            peeked: Seq<Option<I::Item>>,
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Peekable<I> {
            pub fn new(it: I) -> Self {
                Self {
                    iter: it,
                    peeked: seq_empty(),
                }
            }
        }
        // opaque for F*: these hand a value to a caller-supplied closure, and F*
        // cannot see that the closure's output type is the one the body uses (the
        // same reason the `Map` and `Filter` adapters are opaque).
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        #[hax_lib::attributes]
        impl<I: Iterator> Peekable<I> {
            /// See [`std::iter::Peekable::peek`]
            pub fn peek(&mut self) -> Option<&I::Item> {
                if seq_len(&self.peeked) == 0 {
                    let v = self.iter.next();
                    seq_push(&mut self.peeked, v);
                }
                match seq_index(&self.peeked, 0) {
                    Option::Some(v) => Option::Some(v),
                    Option::None => Option::None,
                }
            }

            /// See [`std::iter::Peekable::next_if`]
            pub fn next_if<F: FnOnce(&I::Item) -> bool>(&mut self, func: F) -> Option<I::Item> {
                match Iterator::next(self) {
                    Option::Some(v) => {
                        if func(&v) {
                            Option::Some(v)
                        } else {
                            seq_push(&mut self.peeked, Option::Some(v));
                            Option::None
                        }
                    }
                    Option::None => Option::None,
                }
            }

            /// See [`std::iter::Peekable::next_if_eq`]
            pub fn next_if_eq<T>(&mut self, expected: &T) -> Option<I::Item>
            where
                I::Item: crate::cmp::PartialEq<T>,
            {
                match Iterator::next(self) {
                    Option::Some(v) => {
                        if crate::cmp::PartialEq::eq(&v, expected) {
                            Option::Some(v)
                        } else {
                            seq_push(&mut self.peeked, Option::Some(v));
                            Option::None
                        }
                    }
                    Option::None => Option::None,
                }
            }

            /// See [`std::iter::Peekable::next_if_map`]
            pub fn next_if_map<R, F: FnOnce(I::Item) -> Result<R, I::Item>>(
                &mut self,
                f: F,
            ) -> Option<R> {
                match Iterator::next(self) {
                    Option::Some(v) => match f(v) {
                        Result::Ok(r) => Option::Some(r),
                        Result::Err(v) => {
                            seq_push(&mut self.peeked, Option::Some(v));
                            Option::None
                        }
                    },
                    Option::None => Option::None,
                }
            }
        }
        // `next_if_map_mut` sits in its own block so it can be dropped from both
        // extractions: hax rejects handing a `&mut` to a closure (HAX0003
        // `DirectAndMut`, hacspec/hax#420) and the model's `Fn`/`FnOnce` has no
        // way to hand the mutated element back, so Aeneas's translation of the
        // call does not typecheck either.
        #[cfg(not(hax_backend_fstar))]
        #[cfg_attr(charon, aeneas::exclude)]
        #[hax_lib::attributes]
        impl<I: Iterator> Peekable<I> {
            /// See [`std::iter::Peekable::next_if_map_mut`]
            // std mutates the peeked element in place through `peek_mut`; the
            // model takes the element out, hands `f` a `&mut` to it, and puts it
            // back when `f` declines it. Same observable behaviour.
            pub fn next_if_map_mut<R, F: FnOnce(&mut I::Item) -> Option<R>>(
                &mut self,
                f: F,
            ) -> Option<R> {
                match Iterator::next(self) {
                    Option::Some(mut v) => match f(&mut v) {
                        Option::Some(r) => Option::Some(r),
                        Option::None => {
                            seq_push(&mut self.peeked, Option::Some(v));
                            Option::None
                        }
                    },
                    Option::None => Option::None,
                }
            }
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Iterator for Peekable<I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                if seq_len(&self.peeked) == 0 {
                    self.iter.next()
                } else {
                    seq_remove(&mut self.peeked, 0)
                }
            }
        }
    }
    pub mod intersperse {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_push, seq_remove};
        /// See [`std::iter::Intersperse`]
        // std layers this on `Peekable`; the model keeps its own one-element
        // lookahead in a `Seq` instead, because aeneas hits an internal error on
        // the reference-returning `Peekable::peek` behind a struct field.
        // `Clone` is Rust's own, as for `Cloned`: the separator has to be copied
        // once per gap while staying in the adapter.
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct Intersperse<I: Iterator> {
            separator: I::Item,
            iter: I,
            peeked: Seq<I::Item>,
            exhausted: bool,
            needs_sep: bool,
        }
        #[hax_lib::attributes]
        impl<I: Iterator> Intersperse<I> {
            pub fn new(it: I, separator: I::Item) -> Self {
                Self {
                    separator,
                    iter: it,
                    peeked: seq_empty(),
                    exhausted: false,
                    needs_sep: false,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*, as for `Map`: F* cannot see that the closure's output
        // type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator> Iterator for Intersperse<I>
        where
            I::Item: Clone,
        {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                if seq_len(&self.peeked) == 0 && self.exhausted == false {
                    match self.iter.next() {
                        Option::Some(v) => seq_push(&mut self.peeked, v),
                        Option::None => self.exhausted = true,
                    }
                }
                if self.needs_sep && seq_len(&self.peeked) > 0 {
                    self.needs_sep = false;
                    Option::Some(self.separator.clone())
                } else {
                    self.needs_sep = true;
                    if seq_len(&self.peeked) == 0 {
                        Option::None
                    } else {
                        Option::Some(seq_remove(&mut self.peeked, 0))
                    }
                }
            }
        }
        /// See [`std::iter::IntersperseWith`]
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct IntersperseWith<I: Iterator, G> {
            separator: G,
            iter: I,
            peeked: Seq<I::Item>,
            exhausted: bool,
            needs_sep: bool,
        }
        #[hax_lib::attributes]
        impl<I: Iterator, G> IntersperseWith<I, G> {
            pub fn new(it: I, separator: G) -> Self {
                Self {
                    separator,
                    iter: it,
                    peeked: seq_empty(),
                    exhausted: false,
                    needs_sep: false,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque for F*: as for the `Map` and `Filter` adapters, F* cannot see
        // that the closure's output type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<I: Iterator, G: Fn() -> I::Item> Iterator for IntersperseWith<I, G> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                if seq_len(&self.peeked) == 0 && self.exhausted == false {
                    match self.iter.next() {
                        Option::Some(v) => seq_push(&mut self.peeked, v),
                        Option::None => self.exhausted = true,
                    }
                }
                if self.needs_sep && seq_len(&self.peeked) > 0 {
                    self.needs_sep = false;
                    Option::Some((self.separator)())
                } else {
                    self.needs_sep = true;
                    if seq_len(&self.peeked) == 0 {
                        Option::None
                    } else {
                        Option::Some(seq_remove(&mut self.peeked, 0))
                    }
                }
            }
        }
    }
    pub mod array_chunks {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty, seq_index, seq_len, seq_push};
        use rust_primitives::slice::array_from_fn;
        /// See [`std::iter::ArrayChunks`]
        // std keeps the leftover in `Option<array::IntoIter<I::Item, N>>`; a `Seq`
        // avoids having to move out of a `&mut self` field.
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct ArrayChunks<I: Iterator, const N: usize> {
            iter: I,
            remainder: Seq<I::Item>,
            // Set once the source has run dry, so that further `next` calls cannot
            // overwrite `remainder` with a fresh empty buffer. std gets this for
            // free by holding the leftover in an `Option`.
            // Named `exhausted`, not `done`: Lean opens the enclosing
            // namespaces of a declaration, so a field `done` shadows the
            // ControlFlow constructor that Aeneas's loop translation emits
            // inside this struct's own namespace.
            exhausted: bool,
        }
        #[hax_lib::attributes]
        impl<I: Iterator, const N: usize> ArrayChunks<I, N> {
            // std panics in `Iterator::array_chunks`, this constructor's only caller.
            // Excluded from coverage: `N` is a const parameter, so each width is
            // its own instantiation and no single one can take both arms of the
            // guard — `test_array_chunks_zero_panics` covers `N == 0`, every other
            // test covers `N != 0`.
            #[cfg_attr(coverage_nightly, coverage(off))]
            #[hax_lib::requires(N != 0)]
            pub fn new(it: I) -> Self {
                if N == 0 {
                    crate::panicking::internal::panic()
                }
                Self {
                    iter: it,
                    remainder: seq_empty(),
                    exhausted: false,
                }
            }
        }
        #[hax_lib::attributes]
        // opaque: while-loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        impl<I: Iterator, const N: usize> ArrayChunks<I, N>
        where
            I::Item: Clone,
        {
            /// See [`std::iter::ArrayChunks::into_remainder`]
            // Returns the remainder iterator directly, as current core does; the
            // toolchain this crate is pinned to still wraps it in an `Option`.
            pub fn into_remainder(mut self) -> crate::array::iter::IntoIter<I::Item, N> {
                while let Option::Some(_) = Iterator::next(&mut self) {}
                crate::array::iter::IntoIter(self.remainder)
            }
        }
        #[hax_lib::attributes]
        // opaque: while-loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        impl<I: Iterator, const N: usize> Iterator for ArrayChunks<I, N>
        where
            I::Item: Clone,
        {
            type Item = [I::Item; N];
            // std moves the N elements into an array through `MaybeUninit`; the
            // model has no way to move elements out of its `Seq`, hence the extra
            // `I::Item: Clone` bound and the clone below.
            fn next(&mut self) -> Option<[I::Item; N]> {
                if self.exhausted {
                    return Option::None;
                }
                let mut buf = seq_empty();
                while seq_len(&buf) < N {
                    match self.iter.next() {
                        Option::Some(v) => seq_push(&mut buf, v),
                        Option::None => {
                            self.exhausted = true;
                            self.remainder = buf;
                            return Option::None;
                        }
                    }
                }
                Option::Some(array_from_fn(|i| seq_index(&buf, i).clone()))
            }
        }
    }
    pub mod map_windows {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty, seq_index, seq_len, seq_push, seq_remove};
        use rust_primitives::slice::array_from_fn;
        /// See [`std::iter::MapWindows`]
        // std keeps the sliding window in a `MaybeUninit` ring buffer; the model
        // uses a `Seq` and clones out of it, hence the extra `I::Item: Clone`
        // bound on the `Iterator` impl.
        #[hax_lib::fstar::before("noeq")] // https://github.com/cryspen/hax/issues/1810
        pub struct MapWindows<I: Iterator, F, const N: usize> {
            iter: I,
            f: F,
            window: Seq<I::Item>,
        }
        #[hax_lib::attributes]
        impl<I: Iterator, F, const N: usize> MapWindows<I, F, N> {
            // std panics in `Iterator::map_windows`, this constructor's only caller.
            // Excluded from coverage for the same reason as `ArrayChunks::new`:
            // `N` is a const parameter, so the guard's two arms belong to
            // different instantiations.
            #[cfg_attr(coverage_nightly, coverage(off))]
            #[hax_lib::requires(N != 0)]
            pub fn new(it: I, f: F) -> Self {
                if N == 0 {
                    crate::panicking::internal::panic()
                }
                Self {
                    iter: it,
                    f,
                    window: seq_empty(),
                }
            }
        }
        #[hax_lib::attributes]
        // opaque: while-loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        impl<I: Iterator, R, F: Fn(&[I::Item; N]) -> R, const N: usize> Iterator for MapWindows<I, F, N>
        where
            I::Item: Clone,
        {
            type Item = R;
            fn next(&mut self) -> Option<R> {
                if seq_len(&self.window) == N {
                    seq_remove(&mut self.window, 0);
                }
                while seq_len(&self.window) < N {
                    match self.iter.next() {
                        Option::Some(v) => seq_push(&mut self.window, v),
                        Option::None => return Option::None,
                    }
                }
                let window = array_from_fn(|i| seq_index(&self.window, i).clone());
                Option::Some((self.f)(&window))
            }
        }
    }
    // Out of both extractions: hax rejects a struct that holds a `&mut`
    // (HAX0003 `DirectAndMut`, hacspec/hax#420), and Aeneas threads the borrow
    // back out as an extra closure, which no longer fits the `Iterator` shape.
    #[cfg(not(hax_backend_fstar))]
    pub mod by_ref_sized {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        /// See [`std::iter::ByRefSized`]
        pub struct ByRefSized<'a, I>(pub &'a mut I);
        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        impl<'a, I: Iterator> Iterator for ByRefSized<'a, I> {
            type Item = I::Item;
            fn next(&mut self) -> Option<I::Item> {
                self.0.next()
            }
        }
        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        impl<'a, I: DoubleEndedIterator> DoubleEndedIterator for ByRefSized<'a, I> {
            fn next_back(&mut self) -> Option<I::Item> {
                self.0.next_back()
            }
        }
        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
        impl<'a, I: ExactSizeIterator> ExactSizeIterator for ByRefSized<'a, I> {
            fn len(&self) -> usize {
                ExactSizeIterator::len(self.0)
            }
        }
    }
}

// The iterator sources (`core::iter::{empty, once, repeat, …}`).
//
// Sources that have to hand a *stored* element out by value use
// `rust_primitives::sequence::Seq` as their backing store, the way
// `core::array::IntoIter` and `core::slice::Iter` already do in this model:
// moving out of a `&mut self` field otherwise needs `mem::replace` /
// `Option::take`, both of which are `--exclude`d from the charon run.
pub mod sources {
    pub mod empty {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty};

        /// See [`std::iter::Empty`]
        // std uses `PhantomData<T>`; the model's `PhantomData` stores a `T`, so
        // it cannot be built from nothing. An always-empty `Seq<T>` carries the
        // type parameter instead.
        pub struct Empty<T>(Seq<T>);

        /// See [`std::iter::empty`]
        pub fn empty<T>() -> Empty<T> {
            Empty(seq_empty())
        }

        impl<T> Iterator for Empty<T> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                Option::None
            }
        }

        // opaque for F*: the `Item` of a `DoubleEndedIterator` reaches the record
        // through the (still unresolved) `Iterator` super-instance, so F* will not
        // accept a `next_back` written at the concrete item type.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T> DoubleEndedIterator for Empty<T> {
            fn next_back(&mut self) -> Option<T> {
                Option::None
            }
        }

        impl<T> ExactSizeIterator for Empty<T> {
            fn len(&self) -> usize {
                0
            }
        }
    }

    pub mod once {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_len, seq_one, seq_remove};

        /// See [`std::iter::Once`]
        pub struct Once<T>(Seq<T>);

        /// See [`std::iter::once`]
        pub fn once<T>(value: T) -> Once<T> {
            Once(seq_one(value))
        }

        impl<T> Iterator for Once<T> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    Option::Some(seq_remove(&mut self.0, 0))
                }
            }
        }

        #[hax_lib::attributes]
        // opaque for F*: the `Item` of a `DoubleEndedIterator` reaches the record
        // through the (still unresolved) `Iterator` super-instance, so F* will not
        // accept a `next_back` written at the concrete item type.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T> DoubleEndedIterator for Once<T> {
            fn next_back(&mut self) -> Option<T> {
                let n = seq_len(&self.0);
                if n == 0 {
                    Option::None
                } else {
                    Option::Some(seq_remove(&mut self.0, n - 1))
                }
            }
        }

        impl<T> ExactSizeIterator for Once<T> {
            fn len(&self) -> usize {
                seq_len(&self.0)
            }
        }
    }

    pub mod once_with {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_len, seq_one, seq_remove};

        /// See [`std::iter::OnceWith`]
        pub struct OnceWith<F>(Seq<F>);

        /// See [`std::iter::once_with`]
        pub fn once_with<A, F: FnOnce() -> A>(make: F) -> OnceWith<F> {
            OnceWith(seq_one(make))
        }

        // opaque for F*, as for `Map`: the closure's output type is not visible.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A, F: FnOnce() -> A> Iterator for OnceWith<F> {
            type Item = A;
            fn next(&mut self) -> Option<A> {
                if seq_len(&self.0) == 0 {
                    Option::None
                } else {
                    Option::Some(seq_remove(&mut self.0, 0)())
                }
            }
        }
    }

    pub mod repeat {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;

        /// See [`std::iter::Repeat`]
        // The `Clone` bound is Rust's own (`&self -> Self`), not the model's
        // consuming `crate::clone::Clone`: `next` has to copy the element
        // without giving it up. `core::slice::fill` does the same here.
        pub struct Repeat<A> {
            element: A,
        }

        /// See [`std::iter::repeat`]
        pub fn repeat<A: Clone>(elt: A) -> Repeat<A> {
            Repeat { element: elt }
        }

        impl<A: Clone> Iterator for Repeat<A> {
            type Item = A;
            fn next(&mut self) -> Option<A> {
                Option::Some(self.element.clone())
            }
        }

        // A `Repeat` has no end, so both ends yield the same thing forever.
        // opaque for F*: the `Item` of a `DoubleEndedIterator` reaches the record
        // through the (still unresolved) `Iterator` super-instance, so F* will not
        // accept a `next_back` written at the concrete item type.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A: Clone> DoubleEndedIterator for Repeat<A> {
            fn next_back(&mut self) -> Option<A> {
                Option::Some(self.element.clone())
            }
        }
    }

    pub mod repeat_n {
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;

        /// See [`std::iter::RepeatN`]
        pub struct RepeatN<A> {
            count: usize,
            element: A,
        }

        /// See [`std::iter::repeat_n`]
        pub fn repeat_n<A: Clone>(element: A, count: usize) -> RepeatN<A> {
            RepeatN { count, element }
        }

        impl<A: Clone> Iterator for RepeatN<A> {
            type Item = A;
            fn next(&mut self) -> Option<A> {
                if self.count == 0 {
                    Option::None
                } else {
                    self.count -= 1;
                    // std hands the *stored* element out on the last step
                    // instead of cloning it; the sequence of yielded values is
                    // the same either way.
                    Option::Some(self.element.clone())
                }
            }
        }

        // Every element is the same, so `next_back` behaves like `next`.
        // opaque for F*: the `Item` of a `DoubleEndedIterator` reaches the record
        // through the (still unresolved) `Iterator` super-instance, so F* will not
        // accept a `next_back` written at the concrete item type.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A: Clone> DoubleEndedIterator for RepeatN<A> {
            fn next_back(&mut self) -> Option<A> {
                Iterator::next(self)
            }
        }

        impl<A: Clone> ExactSizeIterator for RepeatN<A> {
            fn len(&self) -> usize {
                self.count
            }
        }
    }

    pub mod repeat_with {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;

        /// See [`std::iter::RepeatWith`]
        pub struct RepeatWith<F> {
            repeater: F,
        }

        /// See [`std::iter::repeat_with`]
        // `FnMut`, like std: a repeater that cannot keep state is useless.
        pub fn repeat_with<A, F: FnMut() -> A>(repeater: F) -> RepeatWith<F> {
            RepeatWith { repeater }
        }

        // opaque for F*, as for `Map`: F* cannot see that the closure's output
        // type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<A, F: FnMut() -> A> Iterator for RepeatWith<F> {
            type Item = A;
            fn next(&mut self) -> Option<A> {
                Option::Some((self.repeater)())
            }
        }
    }

    pub mod from_fn {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;

        /// See [`std::iter::FromFn`]
        pub struct FromFn<F>(F);

        /// See [`std::iter::from_fn`]
        // `FnMut`, like std: a generator that cannot keep state is useless.
        pub fn from_fn<T, F: FnMut() -> Option<T>>(f: F) -> FromFn<F> {
            FromFn(f)
        }

        // opaque for F*, as for `Map`: F* cannot see that the closure's output
        // type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T, F: FnMut() -> Option<T>> Iterator for FromFn<F> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                (self.0)()
            }
        }
    }

    pub mod successors {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_one, seq_push, seq_remove};

        /// See [`std::iter::Successors`]
        // The pending element is held in a `Seq` of length at most one rather
        // than in an `Option`, so that `next` can move it out (see the note on
        // this module).
        pub struct Successors<T, F> {
            next: Seq<T>,
            succ: F,
        }

        /// See [`std::iter::successors`]
        // Excluded from coverage: the arm for a `None` seed is per-instantiation
        // dead code — a caller that passes `None` gets its own monomorphisation,
        // whose `Some` arm is then the unreachable one, so no set of tests covers
        // both arms of any single instantiation.
        #[cfg_attr(coverage_nightly, coverage(off))]
        pub fn successors<T, F: Fn(&T) -> Option<T>>(
            first: Option<T>,
            succ: F,
        ) -> Successors<T, F> {
            let next = match first {
                Option::Some(v) => seq_one(v),
                Option::None => seq_empty(),
            };
            Successors { next, succ }
        }

        // opaque for F*, as for `Map`: F* cannot see that the closure's output
        // type is the one the body uses.
        #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
        impl<T, F: Fn(&T) -> Option<T>> Iterator for Successors<T, F> {
            type Item = T;
            fn next(&mut self) -> Option<T> {
                if seq_len(&self.next) == 0 {
                    Option::None
                } else {
                    let item = seq_remove(&mut self.next, 0);
                    match (self.succ)(&item) {
                        Option::Some(n) => seq_push(&mut self.next, n),
                        Option::None => (),
                    }
                    Option::Some(item)
                }
            }
        }
    }

    // The sources that keep answering `None` once exhausted.
    mod fused {
        use super::super::traits::marker::FusedIterator;
        use crate::option::Option;

        impl<T> FusedIterator for super::empty::Empty<T> {}
        impl<T> FusedIterator for super::once::Once<T> {}
        // Out of F*: the super-instance is `OnceWith`'s `Iterator`, which is
        // opaque there and whose `A` appears only in a refinement, so typeclass
        // resolution cannot instantiate it ("Tactic left uninstantiated
        // unification variable", Error 217).
        #[cfg(not(hax_backend_fstar))]
        impl<A, F: FnOnce() -> A> FusedIterator for super::once_with::OnceWith<F> {}
        impl<A: Clone> FusedIterator for super::repeat::Repeat<A> {}
        impl<A: Clone> FusedIterator for super::repeat_n::RepeatN<A> {}
        impl<T, F: Fn(&T) -> Option<T>> FusedIterator for super::successors::Successors<T, F> {}
    }
}

pub mod range {
    use crate::clone::Clone;
    // // We cannot use core model's PartialOrd because its instances currently have an
    // // `hax_lib::exclude` attribute.
    // use crate::cmp::PartialOrd;
    use crate::option::Option;
    use crate::result::Result;
    /// See [`std::iter::Step`]
    pub trait Step: Clone + PartialOrd<Self> + Sized {
        fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>);
        fn forward_checked(start: Self, count: usize) -> Option<Self>;
        fn backward_checked(start: Self, count: usize) -> Option<Self>;

        fn forward(start: Self, count: usize) -> Self {
            Step::forward_checked(start, count).expect("overflow in `Step::forward`")
        }

        unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
            Step::forward(start, count)
        }

        fn backward(start: Self, count: usize) -> Self {
            Step::backward_checked(start, count).expect("overflow in `Step::backward`")
        }

        unsafe fn backward_unchecked(start: Self, count: usize) -> Self {
            Step::backward(start, count)
        }
    }

    macro_rules! step_signed_methods {
        ($Name:ty, $u:ty) => {
            unsafe fn forward_unchecked(start: Self, n: usize) -> Self {
                unsafe { <$Name>::checked_add_unsigned(start, n as $u).unwrap() }
            }

            unsafe fn backward_unchecked(start: Self, n: usize) -> Self {
                unsafe { <$Name>::checked_sub_unsigned(start, n as $u).unwrap() }
            }
        };
    }

    macro_rules! step_unsigned_methods {
        ($Name:ty) => {
            unsafe fn forward_unchecked(start: Self, n: usize) -> Self {
                unsafe { <$Name>::unchecked_add(start, n as Self) }
            }

            unsafe fn backward_unchecked(start: Self, n: usize) -> Self {
                unsafe { <$Name>::unchecked_sub(start, n as Self) }
            }
        };
    }

    macro_rules! step_identical_methods {
        ($Name:ty) => {
            fn forward(start: Self, n: usize) -> Self {
                Self::forward_checked(start, n).unwrap()
            }

            fn backward(start: Self, n: usize) -> Self {
                Self::backward_checked(start, n).unwrap()
            }
        };
    }

    macro_rules! step_integer_impls {
        {
            narrower than or same width as usize:
                $( [ $UName:ty, $u_narrower:ty, $IName:ty, $i_narrower:ty ] ),+;
            wider than usize:
                $( [ $UName_wide:ty, $u_wider:ty, $IName_wide:ty, $i_wider:ty ] ),+;
        } => {
            $(
                #[hax_lib::attributes]
                impl Step for $u_narrower {
                    step_identical_methods!($UName);
                    step_unsigned_methods!($UName);

                    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                        if *start <= *end {
                            // This relies on $u_narrower <= usize
                            let steps = (*end - *start) as usize;
                            (steps, Option::Some(steps))
                        } else {
                            (0, Option::None)
                        }
                    }

                    // Excluded from coverage: the `Err` arm is per-instantiation
                    // dead code — at the widths where every `usize` fits the type
                    // (`u64`/`u128`/`usize` here) the conversion cannot fail, and
                    // the narrow widths that do reach it are separate
                    // monomorphisations.
                    #[cfg_attr(coverage_nightly, coverage(off))]
                    fn forward_checked(start: Self, n: usize) -> Option<Self> {
                        match <Self as crate::convert::TryFrom<usize>>::try_from(n) {
                            Result::Ok(n) => <$UName>::checked_add(start, n),
                            Result::Err(_) => Option::None, // if n is out of range, `unsigned_start + n` is too
                        }
                    }

                    // Excluded from coverage: the `Err` arm is per-instantiation
                    // dead code — at the widths where every `usize` fits the type
                    // (`u64`/`u128`/`usize` here) the conversion cannot fail, and
                    // the narrow widths that do reach it are separate
                    // monomorphisations.
                    #[cfg_attr(coverage_nightly, coverage(off))]
                    fn backward_checked(start: Self, n: usize) -> Option<Self> {
                        match <Self as crate::convert::TryFrom<usize>>::try_from(n) {
                            Result::Ok(n) => <$UName>::checked_sub(start, n),
                            Result::Err(_) => Option::None, // if n is out of range, `unsigned_start - n` is too
                        }
                    }
                }

                #[hax_lib::attributes]
                impl Step for $i_narrower {
                    step_identical_methods!($IName);
                    step_signed_methods!($IName, $u_narrower);

                    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                        if *start <= *end {
                            // This relies on $i_narrower <= usize.
                            // Casting to isize extends the width but preserves the sign.
                            // Use wrapping_sub in isize space and cast to usize to compute
                            // the difference that might not fit inside the range of isize.
                            let steps = crate::num::isize::wrapping_sub(*end as isize, *start as isize) as usize;
                            (steps, Option::Some(steps))
                        } else {
                            (0, Option::None)
                        }
                    }

                    // Excluded from coverage: both the `Err` arm and the
                    // overflow arm are per-instantiation dead code — at the widths
                    // where every `usize` fits the unsigned counterpart the
                    // conversion cannot fail, and at the narrow ones it cannot
                    // succeed far enough to overflow. Each width is its own
                    // monomorphisation, so no set of tests covers both in one.
                    #[cfg_attr(coverage_nightly, coverage(off))]
                    fn forward_checked(start: Self, n: usize) -> Option<Self> {
                        match <$u_narrower as crate::convert::TryFrom<usize>>::try_from(n) {
                            Result::Ok(n) => {
                                // Wrapping handles cases like
                                // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                                // even though 200 is out of range for i8.
                                let wrapped = <$IName>::wrapping_add(start, n as Self);
                                if wrapped >= start {
                                    Option::Some(wrapped)
                                } else {
                                    Option::None // Addition overflowed
                                }
                            }
                            // If n is out of range of e.g. u8,
                            // then it is bigger than the entire range for i8 is wide
                            // so `any_i8 + n` necessarily overflows i8.
                            Result::Err(_) => Option::None,
                        }
                    }

                    // Excluded from coverage: both the `Err` arm and the
                    // overflow arm are per-instantiation dead code — at the widths
                    // where every `usize` fits the unsigned counterpart the
                    // conversion cannot fail, and at the narrow ones it cannot
                    // succeed far enough to overflow. Each width is its own
                    // monomorphisation, so no set of tests covers both in one.
                    #[cfg_attr(coverage_nightly, coverage(off))]
                    fn backward_checked(start: Self, n: usize) -> Option<Self> {
                        match <$u_narrower as crate::convert::TryFrom<usize>>::try_from(n) {
                            Result::Ok(n) => {
                                // Wrapping handles cases like
                                // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                                // even though 200 is out of range for i8.
                                let wrapped = <$IName>::wrapping_sub(start, n as Self);
                                if wrapped <= start {
                                    Option::Some(wrapped)
                                } else {
                                    Option::None // Subtraction overflowed
                                }
                            }
                            // If n is out of range of e.g. u8,
                            // then it is bigger than the entire range for i8 is wide
                            // so `any_i8 - n` necessarily overflows i8.
                            Result::Err(_) => Option::None,
                        }
                    }
                }
            )+

            $(
                #[hax_lib::attributes]
                impl Step for $u_wider {
                    step_identical_methods!($UName_wide);
                    step_unsigned_methods!($UName_wide);

                    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                        if *start <= *end {
                            match <usize as crate::convert::TryFrom<Self>>::try_from(*end - *start) {
                                Result::Ok(steps) => (steps, Option::Some(steps)),
                                Result::Err(_) => (usize::MAX, Option::None),
                            }
                        } else {
                            (0, Option::None)
                        }
                    }

                    fn forward_checked(start: Self, n: usize) -> Option<Self> {
                        <$UName_wide>::checked_add(start, n as Self)
                    }

                    fn backward_checked(start: Self, n: usize) -> Option<Self> {
                        <$UName_wide>::checked_sub(start, n as Self)
                    }
                }

                #[hax_lib::attributes]
                impl Step for $i_wider {
                    step_identical_methods!($IName_wide);
                    step_signed_methods!($IName_wide, $u_wider);

                    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                        if *start <= *end {
                            match <$IName_wide>::checked_sub(*end, *start) {
                                Option::Some(result) => {
                                    match <usize as crate::convert::TryFrom<$i_wider>>::try_from(result) {
                                        Result::Ok(steps) => (steps, Option::Some(steps)),
                                        Result::Err(_) => (usize::MAX, Option::None),
                                    }
                                }
                                // If the difference is too big for e.g. i128,
                                // it's also gonna be too big for usize with fewer bits.
                                Option::None => (usize::MAX, Option::None),
                            }
                        } else {
                            (0, Option::None)
                        }
                    }

                    fn forward_checked(start: Self, n: usize) -> Option<Self> {
                        <$IName_wide>::checked_add(start, n as Self)
                    }

                    fn backward_checked(start: Self, n: usize) -> Option<Self> {
                        <$IName_wide>::checked_sub(start, n as Self)
                    }
                }
            )+
        };
    }

    // Assuming usize to be 64 bits
    step_integer_impls! {
        narrower than or same width as usize:
            [crate::num::u8, core::primitive::u8, crate::num::i8, core::primitive::i8],
            [crate::num::u16, core::primitive::u16, crate::num::i16, core::primitive::i16],
            [crate::num::u32, core::primitive::u32, crate::num::i32, core::primitive::i32],
            [crate::num::u64, core::primitive::u64, crate::num::i64, core::primitive::i64],
            [crate::num::usize, core::primitive::usize, crate::num::isize, core::primitive::isize];
        wider than usize:
            [crate::num::u128, core::primitive::u128, crate::num::i128, core::primitive::i128];
    }
}

// `DoubleEndedIterator` / `ExactSizeIterator` for the iterators the model
// declares outside this file: `core::ops::range::Range` (its `Iterator` impl
// lives in `core/ops.rs`) and `core::slice::Iter` (in `core/slice.rs`). They are
// collected here so the whole double-ended surface stays in `core::iter`.
mod ends {
    use super::traits::double_ended::DoubleEndedIterator;
    use super::traits::exact_size::ExactSizeIterator;
    use super::traits::iterator::Iterator;
    use crate::ops::range::Range;
    use crate::option::Option;
    use rust_primitives::sequence::{seq_len, seq_remove};

    // `next_back` walks `end` down rather than going through `Step`: the whole
    // `iter::range` module (which holds `Step`) is dropped from the F*
    // extraction, so referring to it from here would dangle.
    macro_rules! range_double_ended {
        ($($int_type: ident)*) => {
            $(
                #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
                // opaque for F*, as for the sources above: `Item` reaches the
                // record through the unresolved `Iterator` super-instance.
                #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
                impl DoubleEndedIterator for Range<$int_type> {
                    fn next_back(&mut self) -> Option<$int_type> {
                        if self.start >= self.end {
                            Option::None
                        } else {
                            self.end -= 1;
                            Option::Some(self.end)
                        }
                    }
                }
            )*
        }
    }

    range_double_ended!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

    // `ExactSizeIterator` is only implemented for the widths where the step
    // count is guaranteed to fit a `usize`, matching core's own list
    // (`range_exact_iter_impl!`), which assumes a 64-bit `usize` for `u32`/`i32`.
    macro_rules! range_exact_size_unsigned {
        ($($int_type: ident)*) => {
            $(
                #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
                impl ExactSizeIterator for Range<$int_type> {
                    fn len(&self) -> usize {
                        if self.start >= self.end {
                            0
                        } else {
                            (self.end - self.start) as usize
                        }
                    }
                }
            )*
        }
    }

    // Signed widths subtract in `isize` and reinterpret as `usize`, the way
    // `Step::steps_between` does, so that e.g. `(i32::MIN..i32::MAX).len()`
    // does not overflow the element type.
    macro_rules! range_exact_size_signed {
        ($($int_type: ident)*) => {
            $(
                #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
                impl ExactSizeIterator for Range<$int_type> {
                    fn len(&self) -> usize {
                        if self.start >= self.end {
                            0
                        } else {
                            crate::num::isize::wrapping_sub(
                                self.end as isize,
                                self.start as isize,
                            ) as usize
                        }
                    }
                }
            )*
        }
    }

    range_exact_size_unsigned!(u8 u16 u32 usize);
    range_exact_size_signed!(i8 i16 i32 isize);

    // opaque for F*, as for the sources above.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    impl<'a, T> DoubleEndedIterator for crate::slice::iter::Iter<'a, T> {
        fn next_back(&mut self) -> Option<&'a T> {
            let n = seq_len(&self.0);
            if n == 0 {
                Option::None
            } else {
                Option::Some(seq_remove(&mut self.0, n - 1))
            }
        }
    }

    impl<'a, T> ExactSizeIterator for crate::slice::iter::Iter<'a, T> {
        fn len(&self) -> usize {
            seq_len(&self.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::traits::iterator::{Iterator, IteratorMethods};
    use crate::option::Option;
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// A simple iterator over a Vec, used to test IteratorMethods.
    /// `Clone` so that a `VecIter<VecIter<_>>` can be built for `flatten`.
    // `Clone` so that `cycle` (which needs to restart the iterator) is testable.
    #[derive(Clone)]
    struct VecIter<T> {
        data: Vec<T>,
        pos: usize,
    }

    impl<T> VecIter<T> {
        fn new(data: Vec<T>) -> Self {
            Self { data, pos: 0 }
        }
    }

    impl<T: Clone> Iterator for VecIter<T> {
        type Item = T;
        fn next(&mut self) -> Option<T> {
            if self.pos < self.data.len() {
                let v = self.data[self.pos].clone();
                self.pos += 1;
                Option::Some(v)
            } else {
                Option::None
            }
        }
    }

    proptest! {
        #[test]
        fn test_fold_sum(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().fold(0i32, |acc, &x| acc.wrapping_add(x));
            let model_result = VecIter::new(v).fold(0i32, |acc: i32, x: i32| acc.wrapping_add(x));
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_fold_collect(v in prop::collection::vec(any::<i32>(), 0..=10)) {
            let std_result: Vec<i32> = v.iter().fold(Vec::new(), |mut acc, &x| { acc.push(x); acc });
            let model_result: Vec<i32> = VecIter::new(v).fold(Vec::new(), |mut acc: Vec<i32>, x: i32| { acc.push(x); acc });
            prop_assert_eq!(model_result, std_result);
        }

        // One test each, not one per outcome: `iter_all`/`iter_any` are generic in
        // the predicate, so a second test would be a second instantiation that
        // only ever takes one of the two exits. `bound` is biased toward the
        // extreme that makes the predicate uniformly true (resp. false).
        #[test]
        fn test_all(
            v in prop::collection::vec(any::<i32>(), 0..=20),
            bound in prop_oneof![Just(i32::MIN), any::<i32>()],
        ) {
            let std_result = v.iter().all(|x| *x > bound);
            let model_result = VecIter::new(v).all(|x: i32| x > bound);
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_any(
            v in prop::collection::vec(any::<i32>(), 0..=20),
            bound in prop_oneof![Just(i32::MAX), any::<i32>()],
        ) {
            let std_result = v.iter().any(|x| *x > bound);
            let model_result = VecIter::new(v).any(|x: i32| x > bound);
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_find(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().find(|x| **x > 10).copied();
            let model_result = VecIter::new(v).find(|x: &i32| *x > 10);
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_find_map(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result: std::option::Option<u32> = v.iter().find_map(|&x| if x > 0 { Some(x as u32) } else { None });
            let model_result: Option<u32> = VecIter::new(v).find_map(|x: i32| if x > 0 { Option::Some(x as u32) } else { Option::None });
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_position(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().position(|x| *x > 10);
            let model_result = VecIter::new(v).position(|x: i32| x > 10);
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_count(v in prop::collection::vec(any::<u8>(), 0..=20)) {
            let std_result = v.iter().count();
            let model_result = VecIter::new(v).count();
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_nth(v in prop::collection::vec(any::<i32>(), 0..=20), n in 0usize..25) {
            let std_result = v.iter().nth(n).copied();
            let model_result = VecIter::new(v).nth(n);
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_last(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().last().copied();
            let model_result = VecIter::new(v).last();
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_for_each(v in prop::collection::vec(any::<i32>(), 0..=5)) {
            // Use a side-effect-free test: for_each with an empty body should consume the iterator
            // without error. We verify it doesn't panic and processes all elements.
            let std_count = std::cell::Cell::new(0usize);
            v.iter().for_each(|_| { std_count.set(std_count.get() + 1); });
            let model_count = std::cell::Cell::new(0usize);
            VecIter::new(v).for_each(|_: i32| { model_count.set(model_count.get() + 1); });
            prop_assert_eq!(model_count.get(), std_count.get());
        }

        #[test]
        fn test_reduce(v in prop::collection::vec(any::<i32>(), 0..=10)) {
            let std_result = v.iter().copied().reduce(|a, b| a.wrapping_add(b));
            let model_result = VecIter::new(v).reduce(|a: i32, b: i32| a.wrapping_add(b));
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_min(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().copied().min();
            let model_result = VecIter::new(v).min();
            prop_assert_eq!(model_result, std_result.inject());
        }

        #[test]
        fn test_max(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().copied().max();
            let model_result = VecIter::new(v).max();
            prop_assert_eq!(model_result, std_result.inject());
        }
    }

    /// The model's `FromIterator::from_iter` gets no bound relating the
    /// iterator's items to `A`, so a collector can consume the iterator but not
    /// read it; `Consumed` records that `collect` reached `from_iter`.
    #[derive(PartialEq, Debug)]
    struct Consumed;

    impl super::traits::collect::FromIterator<u8> for Consumed {
        fn from_iter<T: super::traits::collect::IntoIterator>(iter: T) -> Self {
            let _ = super::traits::collect::IntoIterator::into_iter(iter);
            Consumed
        }
    }

    /// The adapters are lazy; draining them is what observes them.
    fn drain<I: Iterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let Option::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

    proptest! {
        #[test]
        fn test_map(v in prop::collection::vec(any::<u8>(), 0..=20), table in any::<[u8; 256]>()) {
            let f = |x: u8| table[x as usize];
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).map(f)),
                v.iter().map(|&x| f(x)).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_filter(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).filter(|x: &u8| *x > bound)),
                v.iter().copied().filter(|x| *x > bound).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_enumerate(v in prop::collection::vec(any::<u8>(), 0..=20)) {
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).enumerate()),
                v.iter().copied().enumerate().collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_skip(v in prop::collection::vec(any::<u8>(), 0..=20), n in 0usize..=25) {
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).skip(n)),
                v.iter().copied().skip(n).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_take(v in prop::collection::vec(any::<u8>(), 0..=20), n in 0usize..=25) {
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).take(n)),
                v.iter().copied().take(n).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_chain(
            a in prop::collection::vec(any::<u8>(), 0..=10),
            b in prop::collection::vec(any::<u8>(), 0..=10),
        ) {
            prop_assert_eq!(
                drain(VecIter::new(a.clone()).chain(VecIter::new(b.clone()))),
                a.iter().copied().chain(b.iter().copied()).collect::<Vec<_>>()
            );
        }

        // Unequal lengths: `zip` must stop at the shorter side.
        #[test]
        fn test_zip(
            a in prop::collection::vec(any::<u8>(), 0..=10),
            b in prop::collection::vec(any::<u8>(), 0..=15),
        ) {
            prop_assert_eq!(
                drain(VecIter::new(a.clone()).zip(VecIter::new(b.clone()))),
                a.iter().copied().zip(b.iter().copied()).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_flat_map(
            vs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..=5), 0..=6),
        ) {
            prop_assert_eq!(
                drain(VecIter::new(vs.clone()).flat_map(|v: Vec<u8>| VecIter::new(v))),
                vs.iter().flat_map(|v| v.iter().copied()).collect::<Vec<_>>()
            );
        }

        #[test]
        fn test_flatten(
            vs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..=5), 0..=6),
        ) {
            let inner: Vec<VecIter<u8>> = vs.iter().cloned().map(VecIter::new).collect();
            prop_assert_eq!(
                drain(VecIter::new(inner).flatten()),
                vs.iter().flat_map(|v| v.iter().copied()).collect::<Vec<_>>()
            );
        }

        // `IntoIterator for I: Iterator` is the identity.
        #[test]
        fn test_iterator_into_iter(v in prop::collection::vec(any::<u8>(), 0..=20)) {
            use super::traits::collect::IntoIterator;
            prop_assert_eq!(drain(IntoIterator::into_iter(VecIter::new(v.clone()))), v);
        }

        #[test]
        fn test_collect(v in prop::collection::vec(any::<u8>(), 0..=10)) {
            prop_assert_eq!(VecIter::new(v).collect::<Consumed>(), Consumed);
        }

        // `Result<V, E>: FromIterator<Result<A, E>>` delegates to `V`'s own
        // `from_iter`, which is all its (opaque) body claims to do.
        #[test]
        fn test_collect_into_result(v in prop::collection::vec(any::<u8>(), 0..=10)) {
            let it = VecIter::new(v).map(crate::result::Result::<u8, u8>::Ok);
            let collected: crate::result::Result<Consumed, u8> = it.collect();
            prop_assert_eq!(collected, crate::result::Result::Ok(Consumed));
        }

        #[test]
        fn test_step_by(v in prop::collection::vec(any::<u8>(), 0..=20), step in 1usize..=5) {
            prop_assert_eq!(
                drain(VecIter::new(v.clone()).step_by(step)),
                v.iter().copied().step_by(step).collect::<Vec<_>>()
            );
        }
    }

    impl<T: Clone> super::traits::double_ended::DoubleEndedIterator for VecIter<T> {
        fn next_back(&mut self) -> Option<T> {
            if self.pos < self.data.len() {
                Option::Some(self.data.pop().unwrap())
            } else {
                Option::None
            }
        }
    }

    impl<T: Clone> super::traits::exact_size::ExactSizeIterator for VecIter<T> {
        fn len(&self) -> usize {
            self.data.len() - self.pos
        }
    }

    mod double_ended {
        use super::super::traits::double_ended::{DoubleEndedIterator, DoubleEndedIteratorMethods};
        use super::super::traits::exact_size::ExactSizeIterator;
        #[cfg(not(hax_backend_fstar))]
        use super::super::traits::exact_size::ExactSizeIteratorMethods;
        use super::super::traits::iterator::{Iterator, IteratorMethods};
        use super::{VecIter, drain};
        use crate::option::Option;
        use crate::result::Result;
        use crate::testing::Inject;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_rev(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).rev()),
                    v.iter().copied().rev().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_rev_rev(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).rev().rev()),
                    v.iter().copied().rev().rev().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_rev_into_inner(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).rev().into_inner()),
                    v.iter().copied().rev().into_inner().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_rev_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    ExactSizeIterator::len(&VecIter::new(v.clone()).rev()),
                    v.iter().rev().len()
                );
            }

            // `Fuse` has to stay done from the back too, and remember it.
            #[test]
            fn test_fuse_next_back_stays_exhausted(
                v in prop::collection::vec(any::<u8>(), 0..=20),
            ) {
                let mut model = VecIter::new(v.clone()).fuse();
                let mut std_iter = v.iter().copied().fuse();
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    model_out.push(model.next_back());
                    std_out.push(std_iter.next_back().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            // Draining a `chain` from the back has to fall through the second
            // half into the first, and answer `None` once both are done.
            #[test]
            fn test_chain_next_back_through_both_halves(
                a in prop::collection::vec(any::<u8>(), 0..=8),
                b in prop::collection::vec(any::<u8>(), 0..=8),
            ) {
                let mut model = VecIter::new(a.clone()).chain(VecIter::new(b.clone()));
                let mut std_iter = a.iter().copied().chain(b.iter().copied());
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..a.len() + b.len() + 2 {
                    model_out.push(model.next_back());
                    std_out.push(std_iter.next_back().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            // Draining forward first leaves `chain`'s front half taken; a
            // `next_back` after that has to answer from the empty state.
            #[test]
            fn test_chain_next_back_after_forward_drain(
                a in prop::collection::vec(any::<u8>(), 0..=8),
                b in prop::collection::vec(any::<u8>(), 0..=8),
            ) {
                let mut model = VecIter::new(a.clone()).chain(VecIter::new(b.clone()));
                let mut std_iter = a.iter().copied().chain(b.iter().copied());
                for _ in 0..a.len() + b.len() {
                    prop_assert_eq!(Iterator::next(&mut model), std_iter.next().inject());
                }
                prop_assert_eq!(model.next_back(), std_iter.next_back().inject());
            }

            // Alternating ends: the two cursors have to meet in the middle.
            #[test]
            fn test_next_and_next_back(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone());
                let mut std_iter = v.iter().copied();
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for i in 0..v.len() + 2 {
                    if i % 2 == 0 {
                        model_out.push(Iterator::next(&mut model));
                        std_out.push(std_iter.next().inject());
                    } else {
                        model_out.push(model.next_back());
                        std_out.push(std_iter.next_back().inject());
                    }
                }
                prop_assert_eq!(model_out, std_out);
            }

            #[test]
            fn test_nth_back(v in prop::collection::vec(any::<i32>(), 0..=20), n in 0usize..25) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).nth_back(n),
                    v.iter().copied().nth_back(n).inject()
                );
            }

            #[test]
            fn test_rfind(v in prop::collection::vec(any::<i32>(), 0..=20)) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).rfind(|x: &i32| *x > 10),
                    v.iter().copied().rfind(|x| *x > 10).inject()
                );
            }

            // `rfold` with a non-commutative operator, so the order matters.
            #[test]
            fn test_rfold(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let f = |mut acc: Vec<u8>, x: u8| { acc.push(x); acc };
                prop_assert_eq!(
                    VecIter::new(v.clone()).rfold(Vec::new(), f),
                    v.iter().copied().rfold(Vec::new(), f)
                );
            }

            #[test]
            fn test_advance_by(v in prop::collection::vec(any::<u8>(), 0..=20), n in 0usize..25) {
                let mut model = VecIter::new(v.clone());
                let mut std_iter = v.iter().copied();
                let model_res = model.advance_by(n);
                let std_res = std_iter.advance_by(n);
                prop_assert_eq!(
                    match model_res {
                        Result::Ok(()) => Ok(()),
                        Result::Err(k) => Err(k),
                    },
                    std_res.map_err(|k| k.get())
                );
                // Both iterators must be left at the same place.
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<_>>());
            }

            #[test]
            fn test_advance_back_by(
                v in prop::collection::vec(any::<u8>(), 0..=20),
                n in 0usize..25,
            ) {
                let mut model = VecIter::new(v.clone());
                let mut std_iter = v.iter().copied();
                let model_res = model.advance_back_by(n);
                let std_res = std_iter.advance_back_by(n);
                prop_assert_eq!(
                    match model_res {
                        Result::Ok(()) => Ok(()),
                        Result::Err(k) => Err(k),
                    },
                    std_res.map_err(|k| k.get())
                );
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<_>>());
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_rposition(v in prop::collection::vec(any::<i32>(), 0..=20)) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).rposition(|x: i32| x > 10),
                    v.iter().copied().rposition(|x| x > 10).inject()
                );
            }

            #[test]
            fn test_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = VecIter::new(v.clone());
                prop_assert_eq!(ExactSizeIterator::len(&model), v.iter().len());
            }

            // `ExactSizeIteratorMethods` is absent under the F* cfg.
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_is_empty(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = VecIter::new(v.clone());
                prop_assert_eq!(model.is_empty(), v.iter().is_empty());
            }

            // `Range` and `slice::Iter` are the model's own iterators; check the
            // ends of both against std.
            #[test]
            fn test_range_next_back(a in any::<u8>(), b in any::<u8>()) {
                let mut model = crate::ops::range::Range { start: a, end: b };
                let mut std_iter = a..b;
                prop_assert_eq!(model.next_back(), std_iter.next_back().inject());
                prop_assert_eq!(model.next_back(), std_iter.next_back().inject());
            }

            #[test]
            fn test_range_rev(a in any::<u8>(), b in any::<u8>()) {
                prop_assert_eq!(
                    drain(crate::ops::range::Range { start: a, end: b }.rev()),
                    (a..b).rev().collect::<Vec<_>>()
                );
            }

            // One case per width the two `range_exact_size_*` macros cover, so
            // no instantiation is left unexercised.
            #[test]
            fn test_range_len_every_width(a in any::<u8>(), b in any::<u8>()) {
                macro_rules! check {
                    ($($t:ty)*) => { $({
                        let (a, b) = (a as $t, b as $t);
                        prop_assert_eq!(
                            ExactSizeIterator::len(
                                &crate::ops::range::Range { start: a, end: b }
                            ),
                            (a..b).len()
                        );
                    })* };
                }
                check!(u8 u16 u32 usize i8 i16 i32 isize);
            }

            // Likewise for `next_back`, which `range_double_ended!` implements at
            // every width: one instantiation per type, none left unexercised.
            #[test]
            fn test_range_next_back_every_width(a in any::<u8>(), b in any::<u8>()) {
                macro_rules! check {
                    ($($t:ty)*) => { $({
                        let (a, b) = (a as $t, b as $t);
                        let mut model = crate::ops::range::Range { start: a, end: b };
                        let mut std_range = a..b;
                        prop_assert_eq!(model.next_back(), std_range.next_back().inject());
                        // And once more, so an emptied range answers too.
                        prop_assert_eq!(model.next_back(), std_range.next_back().inject());
                    })* };
                }
                check!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);
            }

            #[test]
            fn test_range_len_unsigned(a in any::<u32>(), b in any::<u32>()) {
                prop_assert_eq!(
                    ExactSizeIterator::len(&crate::ops::range::Range { start: a, end: b }),
                    (a..b).len()
                );
            }

            #[test]
            fn test_range_len_signed(a in any::<i32>(), b in any::<i32>()) {
                prop_assert_eq!(
                    ExactSizeIterator::len(&crate::ops::range::Range { start: a, end: b }),
                    (a..b).len()
                );
            }

            #[test]
            fn test_slice_iter_rev(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = crate::slice::iter::Iter(
                    rust_primitives::sequence::seq_from_slice(v.as_slice()),
                );
                prop_assert_eq!(
                    drain(model.rev()).into_iter().copied().collect::<Vec<_>>(),
                    v.iter().rev().copied().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_slice_iter_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = crate::slice::iter::Iter(
                    rust_primitives::sequence::seq_from_slice(v.as_slice()),
                );
                prop_assert_eq!(ExactSizeIterator::len(&model), v.iter().len());
            }

            // The adapters' and sources' double-ended halves.
            #[test]
            fn test_map_rev(
                v in prop::collection::vec(any::<u8>(), 0..=20),
                table in any::<[u8; 256]>(),
            ) {
                let f = |x: u8| table[x as usize];
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).map(f).rev()),
                    v.iter().map(|&x| f(x)).rev().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_map_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = VecIter::new(v.clone()).map(|x: u8| x);
                prop_assert_eq!(ExactSizeIterator::len(&model), v.iter().map(|x| x).len());
            }

            #[test]
            fn test_filter_rev(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).filter(|x: &u8| *x > bound).rev()),
                    v.iter().copied().filter(|x| *x > bound).rev().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_chain_rev(
                a in prop::collection::vec(any::<u8>(), 0..=10),
                b in prop::collection::vec(any::<u8>(), 0..=10),
            ) {
                prop_assert_eq!(
                    drain(VecIter::new(a.clone()).chain(VecIter::new(b.clone())).rev()),
                    a.iter().copied().chain(b.iter().copied()).rev().collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_enumerate_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = VecIter::new(v.clone()).enumerate();
                prop_assert_eq!(ExactSizeIterator::len(&model), v.iter().enumerate().len());
            }

            #[test]
            fn test_once_rev(x in any::<u8>()) {
                prop_assert_eq!(
                    drain(super::super::sources::once::once(x).rev()),
                    std::iter::once(x).rev().collect::<Vec<_>>()
                );
                prop_assert_eq!(
                    ExactSizeIterator::len(&super::super::sources::once::once(x)),
                    std::iter::once(x).len()
                );
            }

            #[test]
            fn test_repeat_n_rev(x in any::<u8>(), n in 0usize..=10) {
                prop_assert_eq!(
                    drain(super::super::sources::repeat_n::repeat_n(x, n).rev()),
                    std::iter::repeat_n(x, n).rev().collect::<Vec<_>>()
                );
                prop_assert_eq!(
                    ExactSizeIterator::len(&super::super::sources::repeat_n::repeat_n(x, n)),
                    std::iter::repeat_n(x, n).len()
                );
            }

            #[test]
            fn test_repeat_next_back(x in any::<u8>()) {
                let mut model = super::super::sources::repeat::repeat(x);
                prop_assert_eq!(model.next_back(), std::iter::repeat(x).next_back().inject());
            }
        }

        #[test]
        fn test_empty_ends() {
            let mut model = super::super::sources::empty::empty::<u8>();
            assert_eq!(model.next_back(), Option::None);
            assert_eq!(
                ExactSizeIterator::len(&model),
                std::iter::empty::<u8>().len()
            );
            #[cfg(not(hax_backend_fstar))]
            assert!(model.is_empty());
        }
    }

    // `Default` and `Extend` for `std::Vec` exist only under `cfg(test)`: the
    // model's collections live in the separate `alloc` crate, which is where the
    // real impls belong. They are enough to exercise `unzip` / `partition` /
    // `collect_into` / `Extend` here.
    impl<T> crate::default::Default for Vec<T> {
        fn default() -> Self {
            Vec::new()
        }
    }

    impl<T> super::traits::collect::Extend<T> for Vec<T> {
        fn extend<It: super::traits::collect::IntoIterator<Item = T>>(&mut self, iter: It)
        where
            It::IntoIter: Iterator<Item = T>,
        {
            let mut it = iter.into_iter();
            while let Option::Some(x) = it.next() {
                self.push(x);
            }
        }
    }

    mod terminal {
        use super::super::traits::collect::{Extend, ExtendMethods};
        use super::super::traits::double_ended::DoubleEndedIteratorMethods;
        use super::super::traits::iterator::IteratorMethods;
        use super::{VecIter, drain};
        use crate::option::Option;
        use crate::result::Result;
        use crate::testing::Inject;
        use proptest::prelude::*;

        /// Items whose comparison key (`.0`) can tie while the values differ, so
        /// that the tie-breaking rules of `min_by`/`max_by` are observable.
        fn keyed(v: &[u8]) -> Vec<(u8, usize)> {
            v.iter().copied().enumerate().map(|(i, x)| (x, i)).collect()
        }

        proptest! {
            // Bounded so neither the model nor std overflows.
            // `sum`/`product` and the comparison family are not part of the
            // F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_sum(v in prop::collection::vec(0..=1000u32, 0..=20)) {
                prop_assert_eq!(
                    IteratorMethods::sum::<u32>(VecIter::new(v.clone())),
                    v.iter().sum::<u32>()
                );
            }

            // `sum`/`product` and the comparison family are not part of the
            // F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            // One width at a time is not enough: `Sum`/`Product` are
            // implemented per integer type, so each has its own body.
            // Not part of the F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            // Small values and few of them: the product has to stay inside `i8`,
            // the narrowest of the widths below.
            fn test_sum_and_product_every_width(v in prop::collection::vec(0u8..=2, 0..=4)) {
                macro_rules! check {
                    ($($t:ty)*) => { $({
                        let v: Vec<$t> = v.iter().map(|x| *x as $t).collect();
                        prop_assert_eq!(
                            IteratorMethods::sum::<$t>(VecIter::new(v.clone())),
                            v.iter().copied().sum::<$t>()
                        );
                        prop_assert_eq!(
                            IteratorMethods::product::<$t>(VecIter::new(v.clone())),
                            v.iter().copied().product::<$t>()
                        );
                    })* };
                }
                check!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);
            }

            // Not part of the F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_product(v in prop::collection::vec(0..=3u64, 0..=20)) {
                prop_assert_eq!(
                    IteratorMethods::product::<u64>(VecIter::new(v.clone())),
                    v.iter().product::<u64>()
                );
            }

            #[test]
            fn test_min_by(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let items = keyed(&v);
                prop_assert_eq!(
                    VecIter::new(items.clone())
                        .min_by(|a: &(u8, usize), b: &(u8, usize)| a.0.cmp(&b.0).inject()),
                    items.iter().copied().min_by(|a, b| a.0.cmp(&b.0)).inject()
                );
            }

            #[test]
            fn test_max_by(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let items = keyed(&v);
                prop_assert_eq!(
                    VecIter::new(items.clone())
                        .max_by(|a: &(u8, usize), b: &(u8, usize)| a.0.cmp(&b.0).inject()),
                    items.iter().copied().max_by(|a, b| a.0.cmp(&b.0)).inject()
                );
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_min_by_key(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let items = keyed(&v);
                prop_assert_eq!(
                    VecIter::new(items.clone()).min_by_key(|x: &(u8, usize)| x.0),
                    items.iter().copied().min_by_key(|x| x.0).inject()
                );
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_max_by_key(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let items = keyed(&v);
                prop_assert_eq!(
                    VecIter::new(items.clone()).max_by_key(|x: &(u8, usize)| x.0),
                    items.iter().copied().max_by_key(|x| x.0).inject()
                );
            }

            // `sum`/`product` and the comparison family are not part of the
            // F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_cmp(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // `a` against itself as well: the walk only takes another step
                // on a pair that compares `Equal`, and two independent draws
                // agree at the same index only by chance.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone()).cmp(VecIter::new(b.clone())),
                        a.iter().cmp(b.iter()).inject()
                    );
                }
            }

            #[test]
            fn test_cmp_by(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // `a` against itself as well: the walk only takes another step
                // on a pair that compares `Equal`, and two independent draws
                // agree at the same index only by chance.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone())
                            .cmp_by(VecIter::new(b.clone()), |x: u8, y: u8| x.cmp(&y).inject()),
                        a.iter().copied().cmp_by(b.iter().copied(), |x, y| x.cmp(&y)).inject()
                    );
                }
            }

            // `sum`/`product` and the comparison family are not part of the
            // F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_partial_cmp(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // `a` against itself as well: only a pair that compares `Equal`
                // makes the walk take another step, and two independent draws
                // agree at the same index only by chance.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone()).partial_cmp(VecIter::new(b.clone())),
                        a.iter().partial_cmp(b.iter()).inject()
                    );
                }
            }

            #[test]
            fn test_partial_cmp_by(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // See `test_cmp`: an equal pair is what makes the walk step.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone()).partial_cmp_by(
                            VecIter::new(b.clone()),
                            |x: u8, y: u8| x.partial_cmp(&y).inject()
                        ),
                        a.iter()
                            .copied()
                            .partial_cmp_by(b.iter().copied(), |x, y| x.partial_cmp(&y))
                            .inject()
                    );
            }
                }

            // `sum`/`product` and the comparison family are not part of the
            // F* model (see the note on `IteratorMethods::sum`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_eq_ne_lt_le_gt_ge(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // See `test_cmp`: an equal pair is what makes the walk step.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone()).eq(VecIter::new(b.clone())),
                        a.iter().eq(b.iter())
                    );
                    prop_assert_eq!(
                        VecIter::new(a.clone()).ne(VecIter::new(b.clone())),
                        a.iter().ne(b.iter())
                    );
                    prop_assert_eq!(
                        VecIter::new(a.clone()).lt(VecIter::new(b.clone())),
                        a.iter().lt(b.iter())
                    );
                    prop_assert_eq!(
                        VecIter::new(a.clone()).le(VecIter::new(b.clone())),
                        a.iter().le(b.iter())
                    );
                    prop_assert_eq!(
                        VecIter::new(a.clone()).gt(VecIter::new(b.clone())),
                        a.iter().gt(b.iter())
                    );
                    prop_assert_eq!(
                        VecIter::new(a.clone()).ge(VecIter::new(b.clone())),
                        a.iter().ge(b.iter())
                    );
                }
            }

            // Same length, one element apart: the element-mismatch exit of
            // `iter_eq_by`, which independent draws reach only by chance.
            #[test]
            fn test_eq_by_same_length_one_apart(
                a in prop::collection::vec(any::<u8>(), 1..=6),
                i in 0usize..6,
            ) {
                let mut one_apart = a.clone();
                let i = i % a.len();
                one_apart[i] = one_apart[i].wrapping_add(1);
                // All four exits of the walk, through one closure so they land in
                // one instantiation: differing (stop early), identical (walk to
                // exhaustion), and either side running out first.
                let shorter = a[..a.len() - 1].to_vec();
                let longer = { let mut v = a.clone(); v.push(0); v };
                for b in [one_apart, a.clone(), shorter, longer] {
                    prop_assert_eq!(
                        VecIter::new(a.clone())
                            .eq_by(VecIter::new(b.clone()), |x: u8, y: u8| x == y),
                        a.iter().copied().eq_by(b.iter().copied(), |x, y| x == y)
                    );
                }
            }

            #[test]
            fn test_eq_by(
                a in prop::collection::vec(any::<u8>(), 0..=6),
                b in prop::collection::vec(any::<u8>(), 0..=6),
            ) {
                // `a` against itself as well: two independent draws differ at the
                // first element almost always, so the walk would never take a
                // second step.
                for b in [b, a.clone()] {
                    prop_assert_eq!(
                        VecIter::new(a.clone())
                            .eq_by(VecIter::new(b.clone()), |x: u8, y: u8| x == y),
                        a.iter().copied().eq_by(b.iter().copied(), |x, y| x == y)
                    );
                }
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_unzip(v in prop::collection::vec((any::<u8>(), any::<i32>()), 0..=20)) {
                let (ma, mb): (Vec<u8>, Vec<i32>) = VecIter::new(v.clone()).unzip();
                let (sa, sb): (Vec<u8>, Vec<i32>) = v.iter().copied().unzip();
                prop_assert_eq!(ma, sa);
                prop_assert_eq!(mb, sb);
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_partition(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                let (myes, mno): (Vec<u8>, Vec<u8>) =
                    VecIter::new(v.clone()).partition(|x: &u8| *x > bound);
                let (syes, sno): (Vec<u8>, Vec<u8>) =
                    v.iter().copied().partition(|x| *x > bound);
                prop_assert_eq!(myes, syes);
                prop_assert_eq!(mno, sno);
            }

            #[test]
            fn test_is_partitioned(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).is_partitioned(|x: u8| x > bound),
                    v.iter().copied().is_partitioned(|x| x > bound)
                );
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_is_sorted(v in prop::collection::vec(0..=3u8, 0..=8)) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).is_sorted(),
                    v.iter().is_sorted()
                );
            }

            #[test]
            fn test_is_sorted_by(v in prop::collection::vec(0..=3u8, 0..=8)) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).is_sorted_by(|a: &u8, b: &u8| a < b),
                    v.iter().copied().is_sorted_by(|a, b| a < b)
                );
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_is_sorted_by_key(v in prop::collection::vec(any::<i8>(), 0..=8)) {
                prop_assert_eq!(
                    VecIter::new(v.clone()).is_sorted_by_key(|x: i8| x.wrapping_abs()),
                    v.iter().copied().is_sorted_by_key(|x| x.wrapping_abs())
                );
            }

            // `collect_into` is not part of the F* model (see its declaration).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_collect_into(
                v in prop::collection::vec(any::<u8>(), 0..=20),
                seed in prop::collection::vec(any::<u8>(), 0..=3),
            ) {
                let mut model = seed.clone();
                VecIter::new(v.clone()).collect_into(&mut model);
                let mut expected = seed.clone();
                v.iter().copied().collect_into(&mut expected);
                prop_assert_eq!(model, expected);
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_next_chunk(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone());
                let mut std_iter = v.iter().copied();
                let m = IteratorMethods::next_chunk::<3>(&mut model);
                let s = std_iter.next_chunk::<3>();
                match (m, s) {
                    (Result::Ok(ma), Ok(sa)) => prop_assert_eq!(ma, sa),
                    (Result::Err(mr), Err(sr)) => {
                        prop_assert_eq!(drain(mr), sr.collect::<Vec<u8>>())
                    }
                    _ => prop_assert!(false, "model and std disagreed on Ok/Err"),
                }
                // Whatever happened, both must be left at the same place.
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_fold(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone());
                let m: Result<u8, ()> = model.try_fold(0u8, |acc: u8, x: u8| {
                    match acc.checked_add(x) {
                        Some(n) => Result::Ok(n),
                        None => Result::Err(()),
                    }
                });
                let mut std_iter = v.iter().copied();
                let s: std::result::Result<u8, ()> =
                    std_iter.try_fold(0u8, |acc, x| acc.checked_add(x).ok_or(()));
                prop_assert_eq!(m, s.inject());
                // A short-circuiting `try_fold` must leave the rest behind.
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_for_each(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                let mut model = VecIter::new(v.clone());
                let m: Result<(), u8> = model.try_for_each(|x: u8| {
                    if x > bound { Result::Err(x) } else { Result::Ok(()) }
                });
                let mut std_iter = v.iter().copied();
                let s: std::result::Result<(), u8> =
                    std_iter.try_for_each(|x| if x > bound { Err(x) } else { Ok(()) });
                prop_assert_eq!(m, s.inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_rfold(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone());
                let m: Result<u8, ()> = model.try_rfold(0u8, |acc: u8, x: u8| {
                    match acc.checked_add(x) {
                        Some(n) => Result::Ok(n),
                        None => Result::Err(()),
                    }
                });
                let mut std_iter = v.iter().copied();
                let s: std::result::Result<u8, ()> =
                    std_iter.try_rfold(0u8, |acc, x| acc.checked_add(x).ok_or(()));
                prop_assert_eq!(m, s.inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            #[test]
            fn test_extend(
                seed in prop::collection::vec(any::<u8>(), 0..=5),
                v in prop::collection::vec(any::<u8>(), 0..=20),
            ) {
                let mut model = seed.clone();
                Extend::extend(&mut model, VecIter::new(v.clone()));
                let mut expected = seed.clone();
                std::iter::Extend::extend(&mut expected, v.iter().copied());
                prop_assert_eq!(model, expected);
            }

            // `Extend::extend_one` / `extend_reserve` are unstable in std, so their
            // documented defaults are pinned directly: push one element, and do
            // nothing at all respectively.
            #[test]
            fn test_extend_one(
                seed in prop::collection::vec(any::<u8>(), 0..=5),
                x in any::<u8>(),
            ) {
                let mut model = seed.clone();
                ExtendMethods::extend_one(&mut model, x);
                let mut expected = seed.clone();
                expected.push(x);
                prop_assert_eq!(model, expected);
            }

            #[test]
            fn test_extend_reserve_is_a_no_op(
                seed in prop::collection::vec(any::<u8>(), 0..=5),
                n in 0usize..=10,
            ) {
                let mut model = seed.clone();
                ExtendMethods::<u8>::extend_reserve(&mut model, n);
                prop_assert_eq!(model, seed);
            }
        }

        /// A `FromIterator` sink for `try_collect`. The model's
        /// `FromIterator::from_iter` cannot walk its argument (its `T: IntoIterator`
        /// bound does not require `T::IntoIter: Iterator`), so no model collection
        /// can record what was collected. The test below therefore pins what
        /// `try_collect` itself decides: whether the run short-circuits, with which
        /// residual, and where it leaves the iterator.
        struct Sink;

        impl<A> super::super::traits::collect::FromIterator<A> for Sink {
            fn from_iter<T: super::super::traits::collect::IntoIterator>(_iter: T) -> Sink {
                Sink
            }
        }

        proptest! {
            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_find(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                // A `0` is what makes the closure answer `Err`, so one input
                // always carries one: otherwise the short-circuit is only
                // exercised when the draw happens to contain a zero.
                let with_zero = { let mut v = v.clone(); v.push(0); v };
                for v in [v, with_zero] {
                    let mut model = VecIter::new(v.clone());
                    let m: Result<Option<u8>, u8> = model.try_find(|x: &u8| {
                        if *x == 0 { Result::Err(*x) } else { Result::Ok(*x > bound) }
                    });
                    let mut std_iter = v.iter().copied();
                    let s: std::result::Result<std::option::Option<u8>, u8> =
                        std_iter.try_find(|x| if *x == 0 { Err(*x) } else { Ok(*x > bound) });
                    prop_assert_eq!(m, s.inject());
                    prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
                }
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_reduce(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone());
                let m: Result<Option<u8>, ()> = model.try_reduce(|a: u8, b: u8| {
                    match a.checked_add(b) {
                        Some(n) => Result::Ok(n),
                        None => Result::Err(()),
                    }
                });
                let mut std_iter = v.iter().copied();
                let s: std::result::Result<std::option::Option<u8>, ()> =
                    std_iter.try_reduce(|a, b| a.checked_add(b).ok_or(()));
                prop_assert_eq!(m, s.inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // Not part of the F* model (see the note on
            // `IteratorMethods::rposition`).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_try_collect(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                let mut model = VecIter::new(v.clone())
                    .map(|x: u8| if x > bound { Result::Err(x) } else { Result::Ok(x) });
                let m: Result<Sink, u8> = model.try_collect();
                let mut std_iter = v
                    .iter()
                    .copied()
                    .map(|x| if x > bound { Err(x) } else { Ok(x) });
                let s: std::result::Result<Vec<u8>, u8> = std_iter.try_collect();
                match (&m, &s) {
                    (Result::Ok(_), Ok(_)) => (),
                    (Result::Err(a), Err(b)) => prop_assert_eq!(a, b),
                    _ => prop_assert!(false, "model and std disagreed on Ok/Err"),
                }
                prop_assert_eq!(
                    drain(model),
                    std_iter.map(|r| r.inject()).collect::<Vec<_>>()
                );
            }
        }

        // Not part of the F* model (see the note on `IteratorMethods::sum`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_sum_overflow_panics() {
            crate::testing::panics_like_core(
                || IteratorMethods::sum::<u8>(VecIter::new(vec![u8::MAX, 1u8])),
                || [u8::MAX, 1u8].into_iter().sum::<u8>(),
            );
        }

        // Not part of the F* model (see the note on `IteratorMethods::sum`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_product_overflow_panics() {
            crate::testing::panics_like_core(
                || IteratorMethods::product::<u8>(VecIter::new(vec![16u8, 16u8])),
                || [16u8, 16u8].into_iter().product::<u8>(),
            );
        }

        // Not part of the F* model (see the note on `IteratorMethods::sum`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_sum_of_empty_is_zero() {
            assert_eq!(
                IteratorMethods::sum::<u32>(VecIter::new(Vec::<u32>::new())),
                std::iter::empty::<u32>().sum::<u32>()
            );
        }

        // Not part of the F* model (see the note on `IteratorMethods::sum`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_product_of_empty_is_one() {
            assert_eq!(
                IteratorMethods::product::<u32>(VecIter::new(Vec::<u32>::new())),
                std::iter::empty::<u32>().product::<u32>()
            );
        }
    }

    mod new_adapters {
        #[cfg(not(hax_backend_fstar))]
        use super::super::adapters::by_ref_sized::ByRefSized;
        use super::super::traits::double_ended::DoubleEndedIterator;
        use super::super::traits::exact_size::ExactSizeIterator;
        use super::super::traits::iterator::{Iterator, IteratorMethods};
        use super::{VecIter, drain};
        use crate::option::Option;
        use crate::result::Result;
        use crate::testing::Inject;
        use proptest::prelude::*;
        use std::cell::Cell;

        /// An iterator over `&u8`, for `cloned` / `copied`.
        fn refs(v: &[u8]) -> VecIter<&u8> {
            VecIter::new(v.iter().collect())
        }

        proptest! {
            #[test]
            fn test_cloned(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(refs(&v).cloned()),
                    v.iter().cloned().collect::<Vec<u8>>()
                );
            }

            #[test]
            fn test_copied(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(refs(&v).copied()),
                    v.iter().copied().collect::<Vec<u8>>()
                );
            }

            // The `DoubleEndedIterator`/`ExactSizeIterator` halves of the three
            // reference-taking adapters: `next` alone never reaches them.
            #[test]
            fn test_cloned_next_back_and_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = refs(&v).cloned();
                let mut std_iter = v.iter().cloned();
                prop_assert_eq!(ExactSizeIterator::len(&model), std_iter.len());
                // Past the end as well, so the exhausted answer is pinned too.
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    model_out.push(model.next_back());
                    std_out.push(std_iter.next_back().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            #[test]
            fn test_copied_next_back_and_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = refs(&v).copied();
                let mut std_iter = v.iter().copied();
                prop_assert_eq!(ExactSizeIterator::len(&model), std_iter.len());
                // Past the end as well, so the exhausted answer is pinned too.
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    model_out.push(model.next_back());
                    std_out.push(std_iter.next_back().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            #[test]
            fn test_inspect_next_back_and_len(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let seen = Cell::new(0usize);
                let mut model = VecIter::new(v.clone()).inspect(|_: &u8| {
                    seen.set(seen.get() + 1)
                });
                let std_seen = Cell::new(0usize);
                let mut std_iter = v
                    .iter()
                    .copied()
                    .inspect(|_| std_seen.set(std_seen.get() + 1));
                prop_assert_eq!(ExactSizeIterator::len(&model), std_iter.len());
                // Past the end as well, so the exhausted answer is pinned too.
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    model_out.push(model.next_back());
                    std_out.push(std_iter.next_back().inject());
                }
                prop_assert_eq!(model_out, std_out);
                prop_assert_eq!(seen.get(), std_seen.get());
            }

            // Once the predicate fails, `take_while` must stay done rather than
            // consult the source again.
            #[test]
            fn test_take_while_stays_exhausted(v in prop::collection::vec(any::<u8>(), 0..=20),
                                               bound in any::<u8>()) {
                let mut model = VecIter::new(v.clone()).take_while(|x: &u8| *x < bound);
                let mut std_iter = v.iter().copied().take_while(|x| *x < bound);
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    model_out.push(Iterator::next(&mut model));
                    std_out.push(std_iter.next().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            // `inspect` must yield every element unchanged *and* run the closure
            // once per element.
            #[test]
            fn test_inspect(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model_seen = Cell::new(0usize);
                let model = drain(VecIter::new(v.clone()).inspect(|_: &u8| {
                    model_seen.set(model_seen.get() + 1)
                }));
                let std_seen = Cell::new(0usize);
                let expected: Vec<u8> = v
                    .iter()
                    .copied()
                    .inspect(|_| std_seen.set(std_seen.get() + 1))
                    .collect();
                prop_assert_eq!(model, expected);
                prop_assert_eq!(model_seen.get(), std_seen.get());
            }

            #[test]
            fn test_filter_map(v in prop::collection::vec(any::<i32>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).filter_map(|x: i32| if x > 0 {
                        Option::Some(x as u32)
                    } else {
                        Option::None
                    })),
                    v.iter()
                        .filter_map(|&x| if x > 0 { Some(x as u32) } else { None })
                        .collect::<Vec<u32>>()
                );
            }

            #[test]
            fn test_map_while(v in prop::collection::vec(any::<i32>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).map_while(|x: i32| if x > 0 {
                        Option::Some(x as u32)
                    } else {
                        Option::None
                    })),
                    v.iter()
                        .map_while(|&x| if x > 0 { Some(x as u32) } else { None })
                        .collect::<Vec<u32>>()
                );
            }

            #[test]
            fn test_skip_while(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).skip_while(|x: &u8| *x < bound)),
                    v.iter().copied().skip_while(|x| *x < bound).collect::<Vec<u8>>()
                );
            }

            #[test]
            fn test_take_while(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).take_while(|x: &u8| *x < bound)),
                    v.iter().copied().take_while(|x| *x < bound).collect::<Vec<u8>>()
                );
            }

            // A running sum that stops once it would overflow: exercises both the
            // state threading and the early `None`.
            // `scan` is not part of the F* model (see its definition).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_scan(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = drain(VecIter::new(v.clone()).scan(0u8, |acc: &mut u8, x: u8| {
                    match acc.checked_add(x) {
                        Some(n) => {
                            *acc = n;
                            Option::Some(n)
                        }
                        None => Option::None,
                    }
                }));
                let expected: Vec<u8> = v
                    .iter()
                    .scan(0u8, |acc, &x| {
                        let n = acc.checked_add(x)?;
                        *acc = n;
                        Some(n)
                    })
                    .collect();
                prop_assert_eq!(model, expected);
            }

            #[test]
            fn test_fuse(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).fuse()),
                    v.iter().copied().fuse().collect::<Vec<u8>>()
                );
            }

            // `Fuse` must keep answering `None` after the first `None`.
            #[test]
            fn test_fuse_stays_none(v in prop::collection::vec(any::<u8>(), 0..=5)) {
                let mut model = VecIter::new(v.clone()).fuse();
                let mut std_iter = v.iter().copied().fuse();
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 3 {
                    model_out.push(Iterator::next(&mut model));
                    std_out.push(std_iter.next().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            #[test]
            fn test_cycle(v in prop::collection::vec(any::<u8>(), 0..=5), n in 0usize..=20) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).cycle().take(n)),
                    v.iter().copied().cycle().take(n).collect::<Vec<u8>>()
                );
            }

            // An empty `cycle` must stay empty rather than loop forever.
            #[test]
            fn test_cycle_empty(n in 0usize..=5) {
                let model: Vec<u8> = drain(VecIter::new(Vec::<u8>::new()).cycle().take(n));
                prop_assert_eq!(model, Vec::<u8>::new());
            }

            #[test]
            fn test_peekable(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone()).peekable();
                let mut std_iter = v.iter().copied().peekable();
                let mut model_out = Vec::new();
                let mut std_out = Vec::new();
                for _ in 0..v.len() + 2 {
                    // Peek twice: the second peek must not consume anything.
                    let peeked = |p: Option<&u8>| match p {
                        Option::Some(v) => Option::Some(*v),
                        Option::None => Option::None,
                    };
                    model_out.push(peeked(model.peek()));
                    model_out.push(peeked(model.peek()));
                    model_out.push(Iterator::next(&mut model));
                    std_out.push(std_iter.peek().copied().inject());
                    std_out.push(std_iter.peek().copied().inject());
                    std_out.push(std_iter.next().inject());
                }
                prop_assert_eq!(model_out, std_out);
            }

            #[test]
            fn test_peekable_next_if(v in prop::collection::vec(any::<u8>(), 0..=20), bound in any::<u8>()) {
                let mut model = VecIter::new(v.clone()).peekable();
                let mut std_iter = v.iter().copied().peekable();
                let model_taken = model.next_if(|x: &u8| *x < bound);
                let std_taken = std_iter.next_if(|x| *x < bound);
                prop_assert_eq!(model_taken, std_taken.inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            #[test]
            fn test_peekable_next_if_eq(v in prop::collection::vec(any::<u8>(), 0..=20), x in any::<u8>()) {
                let mut model = VecIter::new(v.clone()).peekable();
                let mut std_iter = v.iter().copied().peekable();
                prop_assert_eq!(model.next_if_eq(&x), std_iter.next_if_eq(&x).inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // The matching half: a random `u8` almost never equals the head, so
            // the expected value is taken from the sequence itself.
            #[test]
            fn test_peekable_next_if_eq_matches(v in prop::collection::vec(any::<u8>(), 1..=20)) {
                let mut model = VecIter::new(v.clone()).peekable();
                let mut std_iter = v.iter().copied().peekable();
                let head = v[0];
                prop_assert_eq!(
                    model.next_if_eq(&head),
                    std_iter.next_if_eq(&head).inject()
                );
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            #[test]
            fn test_peekable_next_if_map(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone()).peekable();
                let mut std_iter = v.iter().copied().peekable();
                let model_out = model.next_if_map(|x: u8| match x.checked_mul(2) {
                    Some(n) => Result::Ok(n),
                    None => Result::Err(x),
                });
                let std_out = std_iter.next_if_map(|x| x.checked_mul(2).ok_or(x));
                prop_assert_eq!(model_out, std_out.inject());
                prop_assert_eq!(drain(model), std_iter.collect::<Vec<u8>>());
            }

            // `Peekable::next_if_map_mut` landed in std after the toolchain this
            // crate is pinned to, so its documented behaviour is pinned directly:
            // `f` gets a `&mut` to the next element, `Some` consumes it, and
            // `None` leaves the *mutated* element in the iterator.
            // `next_if_map_mut` is not part of the F* model (see its definition).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_peekable_next_if_map_mut(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let mut model = VecIter::new(v.clone()).peekable();
                let model_out = model.next_if_map_mut(|x: &mut u8| {
                    *x = x.wrapping_add(1);
                    if *x % 2 == 0 { Option::Some(*x) } else { Option::None }
                });
                let mut expected_rest = v.clone();
                let expected_out = if v.is_empty() {
                    Option::None
                } else {
                    let bumped = v[0].wrapping_add(1);
                    if bumped % 2 == 0 {
                        expected_rest.remove(0);
                        Option::Some(bumped)
                    } else {
                        expected_rest[0] = bumped;
                        Option::None
                    }
                };
                prop_assert_eq!(model_out, expected_out);
                prop_assert_eq!(drain(model), expected_rest);
            }

            #[test]
            fn test_intersperse(v in prop::collection::vec(any::<u8>(), 0..=20), sep in any::<u8>()) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).intersperse(sep)),
                    v.iter().copied().intersperse(sep).collect::<Vec<u8>>()
                );
            }

            #[test]
            fn test_intersperse_with(v in prop::collection::vec(any::<u8>(), 0..=20), sep in any::<u8>()) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).intersperse_with(|| sep)),
                    v.iter().copied().intersperse_with(|| sep).collect::<Vec<u8>>()
                );
            }

            #[test]
            fn test_array_chunks(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).array_chunks::<3>()),
                    v.iter().copied().array_chunks::<3>().collect::<Vec<[u8; 3]>>()
                );
            }

            #[test]
            fn test_array_chunks_into_remainder(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let model = VecIter::new(v.clone()).array_chunks::<3>().into_remainder();
                // std's `into_remainder` answers with an `Option` on one of the
                // two nightlies CI uses and with the iterator on the other, so
                // the leftover is spelled out: whatever the last full chunk left.
                let expected: Vec<u8> = v[v.len() - v.len() % 3..].to_vec();
                prop_assert_eq!(drain(model), expected);
            }

            // The leftover must survive `next` calls made after exhaustion.
            #[test]
            fn test_array_chunks_remainder_after_extra_next(
                v in prop::collection::vec(any::<u8>(), 0..=20),
            ) {
                let mut model = VecIter::new(v.clone()).array_chunks::<3>();
                while let Option::Some(_) = Iterator::next(&mut model) {}
                Iterator::next(&mut model);
                Iterator::next(&mut model);
                prop_assert_eq!(
                    drain(model.into_remainder()),
                    v[v.len() - v.len() % 3..].to_vec()
                );
            }

            #[test]
            fn test_map_windows(v in prop::collection::vec(any::<u8>(), 0..=20)) {
                let f = |w: &[u8; 3]| w[0].wrapping_add(w[1]).wrapping_add(w[2]);
                prop_assert_eq!(
                    drain(VecIter::new(v.clone()).map_windows(f)),
                    v.iter().copied().map_windows(f).collect::<Vec<u8>>()
                );
            }

            // `by_ref` must leave the rest of the iterator behind.
            // `ByRefSized` is not part of the F* model (see its definition).
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_by_ref(v in prop::collection::vec(any::<u8>(), 0..=20), n in 0usize..=10) {
                let mut model = VecIter::new(v.clone());
                let taken = drain(ByRefSized(model.by_ref()).take(n));
                let rest = drain(model);
                let mut std_iter = v.iter().copied();
                let std_taken: Vec<u8> = std_iter.by_ref().take(n).collect();
                let std_rest: Vec<u8> = std_iter.collect();
                prop_assert_eq!(taken, std_taken);
                prop_assert_eq!(rest, std_rest);
            }

            // The `DoubleEndedIterator`/`ExactSizeIterator` halves of the same
            // wrapper: `by_ref().take(..)` above only drives `next`.
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn test_by_ref_sized_next_back_and_len(
                v in prop::collection::vec(any::<u8>(), 1..=20),
            ) {
                let mut model = VecIter::new(v.clone());
                let mut wrapped = ByRefSized(&mut model);
                let mut std_iter = v.iter().copied();
                prop_assert_eq!(ExactSizeIterator::len(&wrapped), std_iter.len());
                prop_assert_eq!(wrapped.next_back(), std_iter.next_back().inject());
            }

            #[test]
            fn test_enumerate_next_index(v in prop::collection::vec(any::<u8>(), 0..=20), k in 0usize..=10) {
                let mut model = VecIter::new(v.clone()).enumerate();
                let mut std_iter = v.iter().copied().enumerate();
                for _ in 0..k {
                    Iterator::next(&mut model);
                    std_iter.next();
                }
                prop_assert_eq!(model.next_index(), std_iter.next_index());
            }
        }

        // `size_hint` is the trait default `(0, None)` for every model iterator:
        // the model's `Iterator` carries no length information to report. That is
        // a valid (if uninformative) hint for any iterator, so it is pinned here
        // rather than compared against std's per-type answers.
        #[test]
        fn test_size_hint_is_the_default() {
            let it = VecIter::new(vec![1u8, 2, 3]);
            let (lower, upper) = it.size_hint();
            assert_eq!(lower, 0);
            assert_eq!(upper, None::<usize>.inject());
        }

        #[test]
        fn test_array_chunks_zero_panics() {
            crate::testing::panics_like_core(
                || VecIter::new(vec![1u8, 2, 3]).array_chunks::<0>(),
                || [1u8, 2, 3].iter().array_chunks::<0>(),
            );
        }

        #[test]
        fn test_map_windows_zero_panics() {
            crate::testing::panics_like_core(
                || VecIter::new(vec![1u8, 2, 3]).map_windows(|_: &[u8; 0]| 0u8),
                || [1u8, 2, 3].iter().map_windows(|_: &[&u8; 0]| 0u8),
            );
        }
    }

    mod sources {
        use super::super::adapters::{chain::chain, zip::zip};
        use super::super::sources::{
            empty::empty, from_fn::from_fn, once::once, once_with::once_with, repeat::repeat,
            repeat_n::repeat_n, repeat_with::repeat_with, successors::successors,
        };
        use super::super::traits::iterator::{Iterator, IteratorMethods};
        use super::{VecIter, drain};
        use crate::option::Option;
        use crate::testing::Inject;
        use proptest::prelude::*;
        use std::cell::Cell;

        // Observed through `next` rather than `drain`: `drain`'s loop body is
        // counted per instantiation, and an iterator that is always empty gives
        // its own monomorphisation a body no run can enter.
        #[test]
        fn test_empty() {
            let mut model = empty::<u8>();
            let mut std_iter = std::iter::empty::<u8>();
            assert_eq!(Iterator::next(&mut model), std_iter.next().inject());
            assert_eq!(Iterator::next(&mut model), std_iter.next().inject());
        }

        // `successors(None, f)` never calls `f`, so a closure spelled here would
        // be dead code: `up_to_nine` is a named function, exercised below as well.
        // It both continues and stops, which is what reaches either arm of
        // `Successors::next` — a constant successor would only ever reach one,
        // and each successor function is its own instantiation.
        fn up_to_nine(x: &u8) -> Option<u8> {
            if *x < 9 {
                Option::Some(*x + 1)
            } else {
                Option::None
            }
        }

        fn up_to_nine_std(x: &u8) -> std::option::Option<u8> {
            if *x < 9 { Some(*x + 1) } else { None }
        }

        // Same reason as `test_empty`: `successors(None, _)` yields nothing, so
        // it is observed through `next`.
        #[test]
        fn test_successors_none() {
            let mut model = successors(Option::None, up_to_nine);
            let mut std_iter = std::iter::successors(None, up_to_nine_std);
            assert_eq!(Iterator::next(&mut model), std_iter.next().inject());
        }

        // Which is what runs `up_to_nine`/`up_to_nine_std`: a few elements, then
        // the sequence ends — so `drain` gets a non-empty iterator here too.
        #[test]
        fn test_successors_one_step() {
            let model: Vec<u8> = drain(successors(Option::Some(7u8), up_to_nine));
            assert_eq!(
                model,
                std::iter::successors(Some(7u8), up_to_nine_std).collect::<Vec<u8>>()
            );
        }

        #[test]
        fn test_repeat_n_zero() {
            assert_eq!(
                drain(repeat_n(7u8, 0)),
                std::iter::repeat_n(7u8, 0).collect::<Vec<u8>>()
            );
        }

        proptest! {
            #[test]
            fn test_once(x in any::<i32>()) {
                prop_assert_eq!(drain(once(x)), std::iter::once(x).collect::<Vec<_>>());
            }

            #[test]
            fn test_once_with(x in any::<i32>()) {
                prop_assert_eq!(
                    drain(once_with(|| x)),
                    std::iter::once_with(|| x).collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_repeat(x in any::<u8>(), n in 0usize..=10) {
                prop_assert_eq!(
                    drain(repeat(x).take(n)),
                    std::iter::repeat(x).take(n).collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_repeat_n(x in any::<u8>(), n in 0usize..=10) {
                prop_assert_eq!(
                    drain(repeat_n(x, n)),
                    std::iter::repeat_n(x, n).collect::<Vec<_>>()
                );
            }

            // A repeater with state: yields `v`'s elements, then `0`s. Checks the
            // model keeps calling the closure rather than caching its first answer.
            #[test]
            fn test_repeat_with(v in prop::collection::vec(any::<u8>(), 0..=10)) {
                let n = v.len() + 2;
                let i = Cell::new(0usize);
                let model = drain(repeat_with(|| {
                    let k = i.get();
                    i.set(k + 1);
                    v.get(k).copied().unwrap_or(0)
                }).take(n));
                let j = Cell::new(0usize);
                let expected: Vec<u8> = std::iter::repeat_with(|| {
                    let k = j.get();
                    j.set(k + 1);
                    v.get(k).copied().unwrap_or(0)
                }).take(n).collect();
                prop_assert_eq!(model, expected);
            }

            #[test]
            fn test_from_fn(v in prop::collection::vec(any::<u8>(), 0..=10)) {
                let i = Cell::new(0usize);
                let model = drain(from_fn(|| {
                    let k = i.get();
                    i.set(k + 1);
                    match v.get(k) {
                        Some(x) => Option::Some(*x),
                        None => Option::None,
                    }
                }));
                let j = Cell::new(0usize);
                let expected: Vec<u8> = std::iter::from_fn(|| {
                    let k = j.get();
                    j.set(k + 1);
                    v.get(k).copied()
                }).collect();
                prop_assert_eq!(model, expected);
            }

            #[test]
            fn test_successors(x in any::<u32>()) {
                let model = drain(successors(Option::Some(x), |v: &u32| match v.checked_mul(3) {
                    Some(n) => Option::Some(n),
                    None => Option::None,
                }));
                let expected: Vec<u32> =
                    std::iter::successors(Some(x), |v: &u32| v.checked_mul(3)).collect();
                prop_assert_eq!(model, expected);
            }

            #[test]
            fn test_zip_fn(
                a in prop::collection::vec(any::<u8>(), 0..=10),
                b in prop::collection::vec(any::<u8>(), 0..=15),
            ) {
                prop_assert_eq!(
                    drain(zip(VecIter::new(a.clone()), VecIter::new(b.clone()))),
                    std::iter::zip(a, b).collect::<Vec<_>>()
                );
            }

            #[test]
            fn test_chain_fn(
                a in prop::collection::vec(any::<u8>(), 0..=10),
                b in prop::collection::vec(any::<u8>(), 0..=10),
            ) {
                prop_assert_eq!(
                    drain(chain(VecIter::new(a.clone()), VecIter::new(b.clone()))),
                    std::iter::chain(a, b).collect::<Vec<_>>()
                );
            }
        }
    }

    #[test]
    fn test_step_by_zero_panics() {
        crate::testing::panics_like_core(
            || VecIter::new(vec![1u8, 2, 3]).step_by(0),
            || [1u8, 2, 3].iter().step_by(0),
        );
    }

    macro_rules! step_tests {
        ($mod_name:ident, $T:ty) => {
            mod $mod_name {
                use super::super::range::Step as ModelStep;
                use crate::testing::Inject;
                use proptest::prelude::*;
                use std::iter::Step as StdStep;

                proptest! {
                    #[test]
                    fn forward(x: $T, y: $T) {
                        if let Some(n) = <$T as StdStep>::steps_between(&x, &y).1 {
                            prop_assert_eq!(
                                <$T as ModelStep>::forward(x, n),
                                <$T as StdStep>::forward(x, n).inject(),
                            );
                        }
                    }

                    #[test]
                    fn backward(x: $T, y: $T) {
                        if let Some(n) = <$T as StdStep>::steps_between(&x, &y).1 {
                            prop_assert_eq!(
                                <$T as ModelStep>::backward(y, n),
                                <$T as StdStep>::backward(y, n).inject(),
                            );
                        }
                    }

                    #[test]
                    fn forward_unchecked(x: $T, y: $T) {
                        if let Some(n) = <$T as StdStep>::steps_between(&x, &y).1 {
                            prop_assert_eq!(
                                unsafe { <$T as ModelStep>::forward_unchecked(x, n) },
                                unsafe { <$T as StdStep>::forward_unchecked(x, n) }.inject(),
                            );
                        }
                    }

                    #[test]
                    fn backward_unchecked(x: $T, y: $T) {
                        if let Some(n) = <$T as StdStep>::steps_between(&x, &y).1 {
                            prop_assert_eq!(
                                unsafe { <$T as ModelStep>::backward_unchecked(y, n) },
                                unsafe { <$T as StdStep>::backward_unchecked(y, n) }.inject(),
                            );
                        }
                    }

                    #[test]
                    fn steps_between(a: $T, b: $T) {
                        let (model_lower, model_exact) = <$T as ModelStep>::steps_between(&a, &b);
                        let (std_lower, std_exact) = <$T as StdStep>::steps_between(&a, &b);
                        prop_assert_eq!(model_lower, std_lower);
                        prop_assert_eq!(model_exact, std_exact.inject());
                    }

                    // For `u128`/`i128` a random pair never fits in a `usize`, so
                    // the tests above never run these bodies; a small step does.
                    #[test]
                    fn forward_close(x: $T, d in 0usize..=1000) {
                        if <$T as StdStep>::forward_checked(x, d).is_some() {
                            prop_assert_eq!(
                                <$T as ModelStep>::forward(x, d),
                                <$T as StdStep>::forward(x, d).inject(),
                            );
                            prop_assert_eq!(
                                unsafe { <$T as ModelStep>::forward_unchecked(x, d) },
                                unsafe { <$T as StdStep>::forward_unchecked(x, d) }.inject(),
                            );
                        }
                    }

                    #[test]
                    fn backward_close(x: $T, d in 0usize..=1000) {
                        if <$T as StdStep>::backward_checked(x, d).is_some() {
                            prop_assert_eq!(
                                <$T as ModelStep>::backward(x, d),
                                <$T as StdStep>::backward(x, d).inject(),
                            );
                            prop_assert_eq!(
                                unsafe { <$T as ModelStep>::backward_unchecked(x, d) },
                                unsafe { <$T as StdStep>::backward_unchecked(x, d) }.inject(),
                            );
                        }
                    }

                    // For `u128`/`i128` a random pair never fits in a `usize`;
                    // stepping forward by a small amount does.
                    #[test]
                    fn steps_between_close(a: $T, d in 0usize..=1000) {
                        if let Some(b) = <$T as StdStep>::forward_checked(a, d) {
                            let (model_lower, model_exact) = <$T as ModelStep>::steps_between(&a, &b);
                            let (std_lower, std_exact) = <$T as StdStep>::steps_between(&a, &b);
                            prop_assert_eq!(model_lower, std_lower);
                            prop_assert_eq!(model_exact, std_exact.inject());
                        }
                    }

                    #[test]
                    fn forward_checked(x: $T, n: usize) {
                        let model = <$T as ModelStep>::forward_checked(x, n);
                        let std_result = <$T as StdStep>::forward_checked(x, n);
                        prop_assert_eq!(model, std_result.inject());
                    }

                    // A full-range `n` never gets past the `TryFrom<usize>` guard
                    // in the narrow-integer impls, leaving their wrapping-overflow
                    // arm unreached; a narrow `n` reaches both.
                    #[test]
                    fn forward_checked_narrow(x: $T, n in 0usize..=255) {
                        prop_assert_eq!(
                            <$T as ModelStep>::forward_checked(x, n),
                            <$T as StdStep>::forward_checked(x, n).inject(),
                        );
                    }

                    #[test]
                    fn backward_checked_narrow(x: $T, n in 0usize..=255) {
                        prop_assert_eq!(
                            <$T as ModelStep>::backward_checked(x, n),
                            <$T as StdStep>::backward_checked(x, n).inject(),
                        );
                    }

                    #[test]
                    fn backward_checked(x: $T, n: usize) {
                        let model = <$T as ModelStep>::backward_checked(x, n);
                        let std_result = <$T as StdStep>::backward_checked(x, n);
                        prop_assert_eq!(model, std_result.inject());
                    }
                }
            }
        };
    }

    /// Every integer `Step` impl overrides `forward`/`backward` and their
    /// `_unchecked` variants, so the trait's default bodies need a type that
    /// implements only the three required methods.
    mod step_defaults {
        use super::super::range::Step as ModelStep;
        use crate::option::Option;
        use crate::testing::Inject;
        use proptest::prelude::*;
        use std::iter::Step as StdStep;

        #[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
        struct Wrap(u8);

        // Under the F* cfg `crate::clone::Clone` has a blanket impl.
        #[cfg(not(hax_backend_fstar))]
        impl crate::clone::Clone for Wrap {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl ModelStep for Wrap {
            fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                <u8 as ModelStep>::steps_between(&start.0, &end.0)
            }
            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                match <u8 as ModelStep>::forward_checked(start.0, count) {
                    Option::Some(v) => Option::Some(Wrap(v)),
                    Option::None => Option::None,
                }
            }
            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                match <u8 as ModelStep>::backward_checked(start.0, count) {
                    Option::Some(v) => Option::Some(Wrap(v)),
                    Option::None => Option::None,
                }
            }
        }

        proptest! {
            #[test]
            fn steps_between(a in any::<u8>(), b in any::<u8>()) {
                // `Step: Clone` is only a bound, never called by the defaults.
                prop_assert_eq!(crate::clone::Clone::clone(&Wrap(a)), Wrap(a));
                let (model_lower, model_exact) = <Wrap as ModelStep>::steps_between(&Wrap(a), &Wrap(b));
                let (std_lower, std_exact) = <u8 as StdStep>::steps_between(&a, &b);
                prop_assert_eq!(model_lower, std_lower);
                prop_assert_eq!(model_exact, std_exact.inject());
            }

            #[test]
            fn forward(x in any::<u8>(), n in 0usize..=255) {
                prop_assume!(<u8 as StdStep>::forward_checked(x, n).is_some());
                prop_assert_eq!(<Wrap as ModelStep>::forward(Wrap(x), n).0, <u8 as StdStep>::forward(x, n));
                prop_assert_eq!(
                    unsafe { <Wrap as ModelStep>::forward_unchecked(Wrap(x), n) }.0,
                    unsafe { <u8 as StdStep>::forward_unchecked(x, n) }
                );
            }

            #[test]
            fn backward(x in any::<u8>(), n in 0usize..=255) {
                prop_assume!(<u8 as StdStep>::backward_checked(x, n).is_some());
                prop_assert_eq!(<Wrap as ModelStep>::backward(Wrap(x), n).0, <u8 as StdStep>::backward(x, n));
                prop_assert_eq!(
                    unsafe { <Wrap as ModelStep>::backward_unchecked(Wrap(x), n) }.0,
                    unsafe { <u8 as StdStep>::backward_unchecked(x, n) }
                );
            }

            #[test]
            fn forward_checked(x in any::<u8>(), n in any::<usize>()) {
                let model = <Wrap as ModelStep>::forward_checked(Wrap(x), n);
                let expected = <u8 as StdStep>::forward_checked(x, n);
                match (model, expected) {
                    (Option::Some(m), Some(e)) => prop_assert_eq!(m.0, e),
                    (Option::None, None) => {},
                    _ => prop_assert!(false, "forward_checked disagrees"),
                }
            }

            #[test]
            fn backward_checked(x in any::<u8>(), n in any::<usize>()) {
                let model = <Wrap as ModelStep>::backward_checked(Wrap(x), n);
                let expected = <u8 as StdStep>::backward_checked(x, n);
                match (model, expected) {
                    (Option::Some(m), Some(e)) => prop_assert_eq!(m.0, e),
                    (Option::None, None) => {},
                    _ => prop_assert!(false, "backward_checked disagrees"),
                }
            }
        }
    }

    step_tests!(step_u8, u8);
    step_tests!(step_i8, i8);
    step_tests!(step_u16, u16);
    step_tests!(step_i16, i16);
    step_tests!(step_u32, u32);
    step_tests!(step_i32, i32);
    step_tests!(step_u64, u64);
    step_tests!(step_i64, i64);
    step_tests!(step_usize, usize);
    step_tests!(step_isize, isize);
    step_tests!(step_u128, u128);
    step_tests!(step_i128, i128);
}
