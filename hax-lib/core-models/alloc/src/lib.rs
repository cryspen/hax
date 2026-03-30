#![allow(unused)]

#[cfg(test)]
mod testing {
    pub trait Inject {
        type Model;
        fn inject(&self) -> Self::Model;
    }
}

mod alloc {
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub struct Global;
}

mod borrow {
    struct Cow<T>(T);

    pub trait ToOwned {
        fn to_owned(self) -> Self;
    }
    impl<T> ToOwned for T {
        fn to_owned(self) -> Self {
            self
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
    }
}

mod collections {
    // All implementations are dummy (for interfaces only)

    mod binary_heap {
        #[hax_lib::fstar::before("open Rust_primitives.Notations")]
        use crate::vec::*;
        struct BinaryHeap<T, A>(Vec<T, A>);

        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}
        impl BinaryHeap<(), ()> {}

        #[hax_lib::attributes]
        impl<T: Ord, A> BinaryHeap<T, A> {
            fn new() -> BinaryHeap<T, A> {
                BinaryHeap(Vec(
                    rust_primitives::sequence::seq_empty(),
                    std::marker::PhantomData::<A>,
                ))
            }
            #[hax_lib::requires(self.len() < core::primitive::usize::MAX)]
            fn push(&mut self, v: T) {
                self.0.push(v)
            }
            #[hax_lib::ensures(|res| (self.len() > 0) == res.is_some())]
            fn pop(&mut self) -> Option<T> {
                let mut max: Option<&T> = None;
                let mut index = 0;
                for i in 0..self.len() {
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
        }

        #[hax_lib::attributes]
        impl<T: Ord, A> BinaryHeap<T, A> {
            fn len(&self) -> usize {
                self.0.len()
            }

            #[hax_lib::ensures(|res| (self.len() > 0) == res.is_some())]
            fn peek(&self) -> Option<&T> {
                let mut max: Option<&T> = None;
                for i in 0..self.len() {
                    hax_lib::loop_invariant!(|i: usize| (i > 0) == max.is_some());
                    if max.is_none_or(|max| self.0[i] > *max) {
                        max = Some(&self.0[i]);
                    }
                }
                max
            }
        }

        #[hax_lib::fstar::after("
assume val lemma_peek_pop: #t:Type -> (#a: Type) -> (#i: Core_models.Cmp.t_Ord t) -> h: t_BinaryHeap t a
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek #t #a h)]
        ")]
        use core::*;

        #[cfg(test)]
        mod tests {
            use proptest::prelude::*;

            proptest! {
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
        }
    }
    mod btree {
        mod set {
            #[hax_lib::opaque]
            struct BTreeSet<T, U>(Option<T>, Option<U>);

            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}
            impl BTreeSet<(), ()> {}

            impl<T, U> BTreeSet<T, U> {
                fn new() -> BTreeSet<T, U> {
                    BTreeSet(None, None)
                }
            }
        }
    }
    mod vec_deque {
        use rust_primitives::sequence::*;
        pub struct VecDeque<T, A>(pub Seq<T>, std::marker::PhantomData<A>);

        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}
        impl VecDeque<(), ()> {}

        impl<T, A> VecDeque<T, A> {
            #[hax_lib::opaque]
            fn push_back(&mut self, x: T) {}
            fn len(&self) -> usize {
                seq_len(&self.0)
            }
            fn pop_front(&mut self) -> Option<T> {
                if self.len() == 0 {
                    None
                } else {
                    Some(seq_remove(&mut self.0, 0))
                }
            }
        }

        impl<T, A> std::ops::Index<usize> for VecDeque<T, A> {
            type Output = T;
            fn index(&self, i: usize) -> &T {
                seq_index(&self.0, i)
            }
        }
    }
}

mod fmt {
    #[hax_lib::opaque]
    fn format(args: core::fmt::Arguments) -> String {
        String::new()
    }
}

mod slice {
    #[hax_lib::exclude]
    struct Dummy<T>(T);

    use super::vec::Vec;
    use rust_primitives::sequence::*;

    impl<T> Dummy<T> {
        fn to_vec(s: &[T]) -> Vec<T, crate::alloc::Global>
        where
            T: Clone,
        {
            let mut seq = seq_empty();
            seq_extend(&mut seq, s);
            Vec(seq, std::marker::PhantomData::<crate::alloc::Global>)
        }
        fn into_vec<A>(s: Box<[T]>) -> Vec<T, A> {
            Vec(seq_from_boxed_slice(s), std::marker::PhantomData::<A>)
        }
        #[hax_lib::opaque]
        fn sort_by<F: Fn(&T, &T) -> core::cmp::Ordering>(s: &mut [T], compare: F) {}
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
                let model: crate::vec::Vec<u8, crate::alloc::Global> = super::Dummy::<u8>::into_vec(boxed);
                prop_assert_eq!(model.as_slice(), v.as_slice());
            }
        }
    }
}

mod string {
    use rust_primitives::string::*;

    #[cfg_attr(test, derive(PartialEq, Debug))]
    struct String(&'static str);
    impl String {
        fn new() -> Self {
            String("")
        }
        fn push_str(&mut self, other: &'static str) {
            *self = String(str_concat(self.0, other))
        }
        fn push(&mut self, c: char) {
            *self = String(str_concat(self.0, str_of_char(c)))
        }
        fn pop(&mut self) -> Option<char> {
            let l = self.0.len();
            if l > 0 {
                *self = String(str_sub(self.0, 0, l - 1));
                Some(str_index(self.0, l - 1))
            } else {
                None
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::testing::Inject;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn test_push(c in any::<char>()) {
                let mut model = super::String::new();
                let mut std_s = std::string::String::new();
                model.push(c);
                std_s.push(c);
                prop_assert_eq!(model.0, std_s);
            }
        }
        #[test]
        fn test_push_str() {
            let mut model = super::String("hello");
            let mut std_s = "hello".to_string();
            model.push_str("world");
            std_s.push_str("world");
            assert_eq!(model.0, std_s);
        }

        #[test]
        fn test_new() {
            let model = super::String::new();
            assert_eq!(model.0, std::string::String::new());
        }
    }
}

pub mod vec {
    // TODO drain (to be done with iterators)
    use hax_lib::ToInt;
    use rust_primitives::sequence::*;

    #[cfg_attr(test, derive(Debug))]
    pub struct Vec<T, A>(pub Seq<T>, pub std::marker::PhantomData<A>);

    fn from_elem<T: Clone>(item: T, len: usize) -> Vec<T, crate::alloc::Global> {
        Vec(
            seq_create(item, len),
            std::marker::PhantomData::<crate::alloc::Global>,
        )
    }

    #[hax_lib::attributes]
    impl<T> Vec<T, crate::alloc::Global> {
        pub fn new() -> Vec<T, crate::alloc::Global> {
            Vec(
                seq_empty(),
                std::marker::PhantomData::<crate::alloc::Global>,
            )
        }
        pub fn with_capacity(_c: usize) -> Vec<T, crate::alloc::Global> {
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
        #[hax_lib::opaque]
        pub fn truncate(&mut self, n: usize) {}
        #[hax_lib::opaque]
        pub fn swap_remove(&mut self, n: usize) -> T {
            seq_remove(&mut self.0, n)
        }
        #[hax_lib::opaque]
        #[hax_lib::ensures(|_| future(self).len() == new_size)]
        pub fn resize(&mut self, new_size: usize, value: &T) {}
        #[hax_lib::opaque]
        pub fn remove(&mut self, index: usize) -> T {
            seq_remove(&mut self.0, index)
        }
        #[hax_lib::opaque]
        pub fn clear(&mut self) {}
        #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= usize::MAX.to_int())]
        pub fn append(&mut self, other: &mut Vec<T, A>) {
            seq_concat(&mut self.0, &mut other.0);
            other.0 = seq_empty()
        }
        #[hax_lib::opaque]
        pub fn drain<R /* : RangeBounds<usize> */>(&mut self, _range: R) -> drain::Drain<T, A> {
            let l = seq_len(&self.0);
            drain::Drain(seq_drain(&mut self.0, 0, l), std::marker::PhantomData::<A>) // TODO use range bounds
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

    #[hax_lib::attributes]
    impl<T: Clone, A> Vec<T, A> {
        #[hax_lib::requires(seq_len(&self.0).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(&mut self, other: &[T]) {
            seq_extend(&mut self.0, other)
        }
    }

    #[hax_lib::attributes]
    impl<T, A> std::ops::Index<usize> for Vec<T, A> {
        type Output = T;
        #[hax_lib::requires(i < self.len())]
        fn index(&self, i: usize) -> &T {
            seq_index(&self.0, i)
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
    #[hax_lib::opaque]
    impl<T> std::iter::FromIterator<T> for Vec<T, crate::alloc::Global> {
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
    mod tests {
        use crate::testing::Inject;
        use proptest::prelude::*;

        impl<T: Clone> Inject for Vec<T> {
            type Model = super::Vec<T, crate::alloc::Global>;
            fn inject(&self) -> super::Vec<T, crate::alloc::Global> {
                super::Vec::<T, crate::alloc::Global>(
                    rust_primitives::sequence::seq_from_boxed_slice(
                        self.clone().into_boxed_slice(),
                    ),
                    std::marker::PhantomData::<crate::alloc::Global>,
                )
            }
        }

        impl<T: PartialEq, A> PartialEq for super::Vec<T, A> {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        proptest! {
            #[test]
            fn test_len(v in prop::collection::vec(any::<u8>(), 0..100)) {
                prop_assert_eq!(v.inject().len(), v.len());
            }

            #[test]
            fn test_is_empty(v in prop::collection::vec(any::<u8>(), 0..100)) {
                prop_assert_eq!(v.inject().is_empty(), v.is_empty());
            }

            #[test]
            fn test_as_slice(v in prop::collection::vec(any::<u8>(), 0..100)) {
                let model = v.inject();
                prop_assert_eq!(model.as_slice(), v.as_slice());
            }

            #[test]
            fn test_push(v in prop::collection::vec(any::<u8>(), 0..50), x in any::<u8>()) {
                let mut model = v.inject();
                model.push(x);
                let mut std_v = v.clone();
                std_v.push(x);
                prop_assert_eq!(model, std_v.inject());
            }

            #[test]
            fn test_pop(v in prop::collection::vec(any::<u8>(), 0..50)) {
                let mut model = v.inject();
                let mut std_v = v.clone();
                prop_assert_eq!(model.pop(), std_v.pop());
                prop_assert_eq!(model, std_v.inject());
            }

            #[test]
            fn test_index(v in prop::collection::vec(any::<u8>(), 1..50)) {
                let model = v.inject();
                for i in 0..v.len() {
                    prop_assert_eq!(model[i], v[i]);
                }
            }

            #[test]
            fn test_insert(v in prop::collection::vec(any::<u8>(), 0..50), x in any::<u8>(), idx in 0usize..50) {
                if idx <= v.len() {
                    let mut model = v.inject();
                    model.insert(idx, x);
                    let mut std_v = v.clone();
                    std_v.insert(idx, x);
                    prop_assert_eq!(model, std_v.inject());
                }
            }

            #[test]
            fn test_remove(v in prop::collection::vec(any::<u8>(), 1..50), idx in 0usize..50) {
                if idx < v.len() {
                    let mut model = v.inject();
                    let mut std_v = v.clone();
                    prop_assert_eq!(model.remove(idx), std_v.remove(idx));
                    prop_assert_eq!(model, std_v.inject());
                }
            }

            #[test]
            fn test_append(v1 in prop::collection::vec(any::<u8>(), 0..50), v2 in prop::collection::vec(any::<u8>(), 0..50)) {
                let mut model1 = v1.inject();
                model1.append(&mut v2.inject());
                let mut std_v = v1.clone();
                std_v.append(&mut v2.clone());
                prop_assert_eq!(model1, std_v.inject());
            }

            #[test]
            fn test_extend_from_slice(v in prop::collection::vec(any::<u8>(), 0..50), ext in prop::collection::vec(any::<u8>(), 0..50)) {
                let mut model = v.inject();
                model.extend_from_slice(&ext);
                let mut std_v = v.clone();
                std_v.extend_from_slice(&ext);
                prop_assert_eq!(model, std_v.inject());
            }

            #[test]
            fn test_from_elem(x in any::<u8>(), len in 0usize..100) {
                let model = super::from_elem(x, len);
                prop_assert_eq!(model, vec![x; len].inject());
            }
        }

        #[test]
        fn test_new() {
            let model: super::Vec<u8, crate::alloc::Global> = super::Vec::new();
            let std_v: std::vec::Vec<u8> = std::vec::Vec::new();
            assert_eq!(model, std_v.inject());
        }

        #[test]
        fn test_with_capacity() {
            let model: super::Vec<u8, crate::alloc::Global> = super::Vec::with_capacity(10);
            let std_v: std::vec::Vec<u8> = std::vec::Vec::with_capacity(10);
            assert_eq!(model, std_v.inject());
        }
    }
}
