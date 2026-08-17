// This model of iterators doesn't respect the signatures of the original definitions in Rust core.
// We avoid default implementations for trait methods, and instead provide them as external to the trait.
// This means overriding them is not possible.
// We also avoid the coinductivity between `IntoIter` and `Iterator`.

pub mod traits {
    pub mod iterator {
        use super::super::adapters::{
            chain::Chain, enumerate::Enumerate, filter::Filter, flat_map::FlatMap,
            flatten::Flatten, map::Map, skip::Skip, step_by::StepBy, take::Take, zip::Zip,
        };
        use crate::option::Option;
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
        #[cfg_attr(charon, aeneas::exclude)] // forward reference in lean (`core.Usize.Insts.CoreIterRangeStep`)
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

        #[hax_lib::attributes]
        #[cfg_attr(charon, aeneas::exclude)]
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

            fn filter<P: Fn(&Self::Item) -> bool>(self, predicate: P) -> Filter<Self, P> {
                Filter::new(self, predicate)
            }

            fn chain<U: Iterator<Item = Self::Item>>(self, other: U) -> Chain<Self, U> {
                Chain::new(self, other)
            }

            fn skip(self, n: usize) -> Skip<Self> {
                Skip::new(self, n)
            }

            fn any<F: Fn(Self::Item) -> bool>(self, f: F) -> bool {
                iter_any(self, f)
            }

            fn find<P: Fn(&Self::Item) -> bool>(mut self, predicate: P) -> Option<Self::Item> {
                iter_find(&mut self, predicate)
            }

            fn find_map<B, F: Fn(Self::Item) -> Option<B>>(self, f: F) -> Option<B> {
                iter_find_map(self, f)
            }

            fn position<P: Fn(Self::Item) -> bool>(self, predicate: P) -> Option<usize> {
                iter_position(self, predicate)
            }

            fn count(self) -> usize {
                iter_count(self)
            }

            fn nth(self, n: usize) -> Option<Self::Item> {
                iter_nth(self, n)
            }

            fn last(self) -> Option<Self::Item> {
                iter_last(self)
            }

            fn for_each<F: Fn(Self::Item)>(self, f: F) {
                iter_for_each(self, f)
            }

            fn reduce<F: Fn(Self::Item, Self::Item) -> Self::Item>(
                self,
                f: F,
            ) -> Option<Self::Item> {
                iter_reduce(self, f)
            }

            fn min(self) -> Option<Self::Item>
            where
                Self::Item: crate::cmp::Ord,
            {
                iter_min(self)
            }

            fn max(self) -> Option<Self::Item>
            where
                Self::Item: crate::cmp::Ord,
            {
                iter_max(self)
            }

            fn collect<B: super::super::traits::collect::FromIterator<Self::Item>>(self) -> B {
                super::super::traits::collect::FromIterator::from_iter(self)
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

        // TODO rev: DoubleEndedIterator?
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
        #[cfg_attr(charon, aeneas::exclude)]
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
    }

    pub mod once {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_one, seq_remove};

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
    }

    pub mod repeat_n {
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
        impl<A, F: FnOnce() -> A> FusedIterator for super::once_with::OnceWith<F> {}
        impl<A: Clone> FusedIterator for super::repeat::Repeat<A> {}
        impl<A: Clone> FusedIterator for super::repeat_n::RepeatN<A> {}
        impl<T, F: Fn(&T) -> Option<T>> FusedIterator for super::successors::Successors<T, F> {}
    }
}

pub mod range {
    use crate::clone::Clone;
    // // We cannot use core model's PartialOrd because its instances currently have an
    // // `aeneas::exclude` attribute.
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

                    fn forward_checked(start: Self, n: usize) -> Option<Self> {
                        match <Self as crate::convert::TryFrom<usize>>::try_from(n) {
                            Result::Ok(n) => <$UName>::checked_add(start, n),
                            Result::Err(_) => Option::None, // if n is out of range, `unsigned_start + n` is too
                        }
                    }

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

#[cfg(test)]
mod tests {
    use super::traits::iterator::{Iterator, IteratorMethods};
    use crate::option::Option;
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// A simple iterator over a Vec, used to test IteratorMethods.
    /// `Clone` so that a `VecIter<VecIter<_>>` can be built for `flatten`.
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

    mod sources {
        use super::super::adapters::{chain::chain, zip::zip};
        use super::super::sources::{
            empty::empty, from_fn::from_fn, once::once, once_with::once_with, repeat::repeat,
            repeat_n::repeat_n, repeat_with::repeat_with, successors::successors,
        };
        use super::super::traits::iterator::IteratorMethods;
        use super::{VecIter, drain};
        use crate::option::Option;
        use proptest::prelude::*;
        use std::cell::Cell;

        #[test]
        fn test_empty() {
            assert_eq!(
                drain(empty::<u8>()),
                std::iter::empty::<u8>().collect::<Vec<u8>>()
            );
        }

        #[test]
        fn test_successors_none() {
            let model: Vec<u8> = drain(successors(Option::None, |x: &u8| Option::Some(*x)));
            assert_eq!(
                model,
                std::iter::successors(None, |x: &u8| Some(*x)).collect::<Vec<u8>>()
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
            fn clone(self) -> Self {
                self
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
                prop_assert_eq!(crate::clone::Clone::clone(Wrap(a)), Wrap(a));
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
