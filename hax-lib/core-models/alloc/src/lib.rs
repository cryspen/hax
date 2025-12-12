mod alloc {
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
    pub struct Box<T, A>(pub T, pub Option<A>);
    impl<T, A> Box<T, A> {
        fn new(v: T) -> Box<T, A> {
            Box(v, None)
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
                    Some(seq_last(&self.0))
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
        fn to_vec(s: &[T]) -> Vec<T, crate::alloc::Global> {
            Vec(
                seq_from_slice(s),
                std::marker::PhantomData::<crate::alloc::Global>,
            )
        }
        fn into_vec<A>(s: super::boxed::Box<&[T], A>) -> Vec<T, A> {
            Vec(seq_from_slice(s.0), std::marker::PhantomData::<A>)
        }
        #[hax_lib::opaque]
        fn sort_by<F: Fn(&T, &T) -> core::cmp::Ordering>(s: &mut [T], compare: F) {}
    }
}

mod string {
    use rust_primitives::string::*;

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
}

pub mod vec {
    // TODO drain (to be done with iterators)
    use hax_lib::ToInt;
    use rust_primitives::sequence::*;

    pub struct Vec<T, A>(pub Seq<T>, pub std::marker::PhantomData<A>);

    #[hax_lib::attributes]
    impl<T> Vec<T, crate::alloc::Global> {
        pub fn new() -> Vec<T, crate::alloc::Global> {
            Vec(
                seq_empty(),
                std::marker::PhantomData::<crate::alloc::Global>,
            )
        }
        pub fn with_capacity() -> Vec<T, crate::alloc::Global> {
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
            seq_concat(&mut self.0, &seq_one(x))
        }
        pub fn pop(&mut self) -> Option<T> {
            if seq_len(&self.0) > 0 {
                let last = seq_last(&self.0);
                self.0 = seq_slice(&self.0, 0, seq_len(&self.0) - 1);
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
            let mut left = seq_slice(&self.0, 0, index);
            let right = seq_slice(&self.0, index, seq_len(&self.0));
            seq_concat(&mut left, &seq_one(element));
            seq_concat(&mut left, &right);
            self.0 = left;
        }
        pub fn as_slice(&self) -> &[T] {
            seq_to_slice(&self.0)
        }
        #[hax_lib::opaque]
        pub fn truncate(&mut self, n: usize) {}
        #[hax_lib::opaque]
        pub fn swap_remove(&mut self, n: usize) -> T {
            seq_last(&self.0)
        }
        #[hax_lib::opaque]
        #[hax_lib::ensures(|_| future(self).len() == new_size)]
        pub fn resize(&mut self, new_size: usize, value: &T) {}
        #[hax_lib::opaque]
        pub fn remove(&mut self, index: usize) -> T {
            seq_last(&self.0)
        }
        #[hax_lib::opaque]
        pub fn clear(&mut self) {}
        #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= usize::MAX.to_int())]
        pub fn append(&mut self, other: &mut Vec<T, A>) {
            seq_concat(&mut self.0, &other.0);
            other.0 = seq_empty()
        }
        #[hax_lib::opaque]
        pub fn drain<R /* : RangeBounds<usize> */>(&mut self, _range: R) -> drain::Drain<T, A> {
            drain::Drain(seq_slice(&self.0, 0, self.len()), std::marker::PhantomData::<A>) // TODO use range bounds
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
                let res = seq_first(&self.0);
                self.0 = seq_slice(&self.0, 1, seq_len(&self.0));
                Option::Some(res)
            }
        }
        }
    }

    #[hax_lib::attributes]
    impl<T, A> Vec<T, A> {
        #[hax_lib::requires(seq_len(&s.0).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(s: &mut Vec<T, A>, other: &[T]) {
            seq_concat(&mut s.0, &seq_from_slice(other))
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
}
