// This model of iterators doesn't respect the signatures of the original definitions in Rust core.
// We avoid default implementations for trait methods, and instead provide them as external to the trait.
// This means overriding them is not possible.
// We also avoid the coinductivity between `IntoIter` and `Iterator`.

pub mod traits {
    pub mod iterator {
        use super::super::adapters::{
            enumerate::Enumerate, flat_map::FlatMap, flatten::Flatten, map::Map, step_by::StepBy,
            take::Take, zip::Zip,
        };
        use crate::ops::function::*;
        use crate::option::Option;
        #[hax_lib::attributes]
        pub trait Iterator {
            type Item;
            #[hax_lib::requires(true)]
            fn next(&mut self) -> Option<Self::Item>;
        }
        #[hax_lib::opaque]
        fn fold<I: Iterator, B, F: FnOnce<(B, I::Item), Output = B>>(
            mut it: I,
            init: B,
            f: F,
        ) -> B {
            let mut accum = init;
            while let Option::Some(x) = it.next() {
                accum = f.call_once((accum, x));
            }
            accum
        }

        fn enumerate<I: Iterator>(it: I) -> Enumerate<I> {
            Enumerate::new(it)
        }

        fn step_by<I: Iterator>(it: I, step: usize) -> StepBy<I> {
            StepBy::new(it, step)
        }

        fn map<I: Iterator, O, F: FnOnce<I::Item, Output = O>>(it: I, f: F) -> Map<I, F> {
            Map::new(it, f)
        }

        #[hax_lib::opaque]
        fn all<I: Iterator, F: FnOnce<I::Item, Output = bool>>(mut it: I, f: F) -> bool {
            while let Option::Some(x) = it.next() {
                if !f.call_once(x) {
                    return false;
                }
            }
            true
        }

        fn take<I: Iterator>(it: I, n: usize) -> Take<I> {
            Take::new(it, n)
        }

        fn flat_map<I: Iterator, U: Iterator, F: FnOnce<I::Item, Output = U>>(
            it: I,
            f: F,
        ) -> FlatMap<I, U, F> {
            FlatMap::new(it, f)
        }

        fn flatten<I: Iterator>(it: I) -> Flatten<I>
        where
            I::Item: Iterator,
        {
            Flatten::new(it)
        }

        fn zip<I1: Iterator, I2: Iterator>(it1: I1, it2: I2) -> Zip<I1, I2> {
            Zip::new(it1, it2)
        }

        // TODO rev: DoubleEndedIterator?
    }
    pub mod collect {
        pub trait IntoIterator {
            // Ignoring type Item, and trait bound Iterator to avoid coinduction
            // type Item;
            type IntoIter; //: Iterator<Item = Self::Item>
            fn into_iter(self) -> Self::IntoIter;
        }
    }
}

pub mod adapters {
    pub mod enumerate {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        pub struct Enumerate<I> {
            iter: I,
            count: usize,
        }
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
        use crate::ops::function::*;
        use crate::option::Option;
        impl<I: Iterator, O, F: FnOnce<I::Item, Output = O>> Iterator for Map<I, F> {
            type Item = O;

            fn next(&mut self) -> Option<O> {
                match self.iter.next() {
                    Option::Some(v) => Option::Some(self.f.call_once(v)),
                    Option::None => Option::None,
                }
            }
        }
    }
    pub mod take {
        use super::super::traits::iterator::Iterator;
        use crate::option::Option;
        pub struct Take<I> {
            iter: I,
            n: usize,
        }
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
        pub struct FlatMap<I, U, F> {
            it: I,
            f: F,
            current: Option<U>,
        }
        impl<I: Iterator, U: Iterator, F: FnOnce<I::Item, Output = U>> FlatMap<I, U, F> {
            pub fn new(it: I, f: F) -> Self {
                Self {
                    it,
                    f,
                    current: Option::None,
                }
            }
        }
        use crate::ops::function::*;
        #[hax_lib::opaque]
        impl<I: Iterator, U: Iterator, F: FnOnce<I::Item, Output = U>> Iterator for FlatMap<I, U, F> {
            type Item = U::Item;
            fn next(&mut self) -> Option<U::Item> {
                loop {
                    if let Option::Some(current_it) = &mut self.current
                        && let Option::Some(v) = current_it.next()
                    {
                        return Option::Some(v);
                    } else {
                        match self.it.next() {
                            Option::Some(c) => self.current = Option::Some(self.f.call_once(c)),
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
}
