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
        pub(crate) trait IteratorMethods: Iterator {
            fn fold<B, F: Fn(B, Self::Item) -> B>(self, init: B, f: F) -> B;
            fn enumerate(self) -> Enumerate<Self>
            where
                Self: Sized;
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_fold<I: Iterator, B, F: Fn(B, I::Item) -> B>(mut iter: I, init: B, f: F) -> B {
            let mut accum = init;
            while let Option::Some(x) = iter.next() {
                accum = f(accum, x);
            }
            accum
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_all<I: Iterator, F: Fn(I::Item) -> bool>(mut iter: I, f: F) -> bool {
            while let Option::Some(x) = iter.next() {
                if !f(x) {
                    return false;
                }
            }
            true
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_any<I: Iterator, F: Fn(I::Item) -> bool>(mut iter: I, f: F) -> bool {
            while let Option::Some(x) = iter.next() {
                if f(x) {
                    return true;
                }
            }
            false
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_count<I: Iterator>(mut iter: I) -> usize {
            let mut n: usize = 0;
            while let Option::Some(_) = iter.next() {
                n += 1;
            }
            n
        }

        // opaque: for-loop generates Rust_primitives.Hax.Folds, causing F* dependency cycle
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_nth<I: Iterator>(mut iter: I, n: usize) -> Option<I::Item> {
            for _ in 0..n {
                if let Option::None = iter.next() {
                    return Option::None;
                }
            }
            iter.next()
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_last<I: Iterator>(mut iter: I) -> Option<I::Item> {
            let mut last = Option::None;
            while let Option::Some(x) = iter.next() {
                last = Option::Some(x);
            }
            last
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        fn iter_for_each<I: Iterator, F: Fn(I::Item)>(mut iter: I, f: F) {
            while let Option::Some(x) = iter.next() {
                f(x);
            }
        }

        // opaque: while-let loop is not supported by hax FunctionalizeLoops
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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
        #[hax_lib::opaque]
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
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

        #[cfg_attr(charon, aeneas::exclude)]
        impl<I: Iterator> IteratorMethods for I {
            fn fold<B, F: Fn(B, I::Item) -> B>(self, init: B, f: F) -> B {
                iter_fold(self, init, f)
            }

            fn enumerate(self) -> Enumerate<I> {
                Enumerate::new(self)
            }

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

        impl<I: Iterator> super::collect::IntoIterator for I {
            type Item = I::Item;
            type IntoIter = Self;
            fn into_iter(self) -> Self {
                self
            }
        }

        // TODO rev: DoubleEndedIterator?
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
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        impl<I> Enumerate<I> {
            pub fn new(iter: I) -> Enumerate<I> {
                Enumerate { iter, count: 0 }
            }
        }
        impl<I: Iterator> Iterator for Enumerate<I> {
            type Item = (usize, <I as Iterator>::Item);

            fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
                match self.iter.next() {
                    Option::Some(a) => {
                        let i = self.count;
                        // TODO check what to do here. It would be bad to have an iterator with
                        // more than usize::MAX elements, this could be a requirement (but hard to formulate).
                        hax_lib::assume!(self.count < usize::MAX);
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

        impl<I> StepBy<I> {
            pub fn new(iter: I, step: usize) -> Self {
                StepBy { iter, step }
            }
        }

        #[hax_lib::opaque]
        impl<I: Iterator> Iterator for StepBy<I> {
            type Item = <I as Iterator>::Item;

            fn next(&mut self) -> Option<<I as Iterator>::Item> {
                for _ in 1..self.step {
                    if let Option::None = self.iter.next() {
                        return Option::None;
                    }
                }
                self.iter.next()
            }
        }
    }
    pub mod map {
        /// See [`std::iter::Map`]
        pub struct Map<I, F> {
            iter: I,
            f: F,
        }

        impl<I, F> Map<I, F> {
            pub fn new(iter: I, f: F) -> Self {
                Self { iter, f }
            }
        }
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
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
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        impl<I> Take<I> {
            pub fn new(iter: I, n: usize) -> Take<I> {
                Take { iter, n }
            }
        }
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
        impl<I: Iterator, U: Iterator, F: Fn(I::Item) -> U> FlatMap<I, U, F> {
            pub fn new(it: I, f: F) -> Self {
                Self {
                    it,
                    f,
                    current: Option::None,
                }
            }
        }
        #[hax_lib::opaque]
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
        #[hax_lib::opaque]
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
        impl<I1: Iterator, I2: Iterator> Zip<I1, I2> {
            pub fn new(it1: I1, it2: I2) -> Self {
                Self { it1, it2 }
            }
        }
        #[hax_lib::opaque]
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
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        impl<I, P> Filter<I, P> {
            pub fn new(iter: I, predicate: P) -> Self {
                Self { iter, predicate }
            }
        }
        // opaque: loop + Fn output projection not provably bool in F*
        #[hax_lib::opaque]
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
        impl<A: Iterator, B: Iterator<Item = A::Item>> Chain<A, B> {
            pub fn new(a: A, b: B) -> Self {
                Self {
                    a: Option::Some(a),
                    b,
                }
            }
        }
        // opaque: `ref mut` pattern in if-let is not supported by hax
        #[hax_lib::opaque]
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
        #[cfg_attr(charon, aeneas::exclude)] // https://github.com/AeneasVerif/aeneas/issues/1098
        impl<I> Skip<I> {
            pub fn new(iter: I, n: usize) -> Self {
                Self { iter, n }
            }
        }
        // opaque: while-loop generates Rust_primitives.Hax.while_loop, causing F* dependency cycle
        #[hax_lib::opaque]
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

        #[test]
        fn test_all_true(v in prop::collection::vec(0..=100i32, 0..=20)) {
            let std_result = v.iter().all(|x| *x >= 0);
            let model_result = VecIter::new(v).all(|x: i32| x >= 0);
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_all_false(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().all(|x| *x > 0);
            let model_result = VecIter::new(v).all(|x: i32| x > 0);
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_any_true(v in prop::collection::vec(any::<i32>(), 0..=20)) {
            let std_result = v.iter().any(|x| *x > 0);
            let model_result = VecIter::new(v).any(|x: i32| x > 0);
            prop_assert_eq!(model_result, std_result);
        }

        #[test]
        fn test_any_false(v in prop::collection::vec(0..=0i32, 0..=10)) {
            let std_result = v.iter().any(|x| *x > 0);
            let model_result = VecIter::new(v).any(|x: i32| x > 0);
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

                    #[test]
                    fn forward_checked(x: $T, n: usize) {
                        let model = <$T as ModelStep>::forward_checked(x, n);
                        let std_result = <$T as StdStep>::forward_checked(x, n);
                        prop_assert_eq!(model, std_result.inject());
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
