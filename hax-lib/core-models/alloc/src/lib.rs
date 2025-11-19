mod alloc {
    pub struct Global;
}

mod borrow {
    struct Cow<T>(T);

    pub trait ToOwned {
        fn to_owned(self) -> Self;
    }
    impl <T> ToOwned for T {
        fn to_owned(self) -> Self {
            self
        }
    }
}

mod boxed {
    struct Box<T, A>(T, Option<A>);
    impl <T, A> Box<T, A> {
        fn new(v: T) -> Box<T, A> {
            Box(v, None)
        }
    }
}

mod collections {
    // All implementations are dummy (for interfaces only)

    mod binary_heap {
        #[hax_lib::opaque]
        struct BinaryHeap<T, U>(Option<T>, Option<U>);

        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}
        impl BinaryHeap<(),()> {}

        impl <T, U> BinaryHeap<T, U> {
            fn new() -> BinaryHeap<T, U> {
                BinaryHeap(None, None)
            }
            fn push(self, v: T) -> Self {
                self
            }
            fn pop(self) -> (Self, Option<T>) {
                (self, None)
            }
        }
    }
    mod btree {
        mod set {
            #[hax_lib::opaque]
            struct BTreeSet<T, U>(Option<T>, Option<U>);

            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}
            impl BTreeSet<(),()> {}

            impl <T, U> BTreeSet<T, U> {
                fn new() -> BTreeSet<T, U> {
                    BTreeSet(None, None)
                }
            }

        }
    }
    mod vec_deque {
        use rust_primitives::seq::*;
        pub struct VecDeque<T, A>(pub Seq<T, A>);

        impl VecDeque<(),()> {}        
        impl VecDeque<(),()> {}        
        impl VecDeque<(),()> {}
        impl VecDeque<(),()> {}
        impl VecDeque<(),()> {}

        impl <T, A> VecDeque<T, A> {
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
        
        impl <T, A> std::ops::Index<usize> for VecDeque<T, A> {
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
    struct Dummy;

    use super::vec::Vec;
    use rust_primitives::seq::*;

    impl Dummy {
        fn to_vec<T>(s: &[T]) -> Vec<T, crate::alloc::Global> {
            Vec(seq_from_slice(s))
        }
        fn into_vec<T, A>(s: super::boxed::Box<&[T], A>) -> Vec<T, A> {
            Vec(seq_from_slice(s.0))
        }
        #[hax_lib::opaque]
        fn sort_by<T, F: Fn(&T, &T) -> core::cmp::Ordering>(s: &mut [T], compare: F) {}
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
    use rust_primitives::seq::*;
    use hax_lib::ToInt;

    pub struct Vec<T, A>(pub Seq<T, A>);

    impl <T> Vec<T, crate::alloc::Global> {
        fn new() -> Vec<T, crate::alloc::Global> {
            Vec(seq_empty())
        }
        fn with_capacity() -> Vec<T, crate::alloc::Global> {
            Vec(seq_empty())
        }
    }

    #[hax_lib::attributes]
    impl <T, A> Vec<T, A> {
        fn len(&self) -> usize {
            seq_len(&self.0)
        }
        #[hax_lib::requires(seq_len(&self.0) < usize::MAX)]
        fn push(&mut self, x: T) {
            seq_concat(&mut self.0, &seq_one(x))
        } 
        fn pop(&mut self) -> Option<T> {
            if seq_len(&self.0) == 0 {
                None
            } else {
                self.0 = seq_slice(&self.0, 0, seq_len(&self.0) - 1);
                Some(seq_last(&self.0))
            }
        }
        fn is_empty(&self) -> bool {
            seq_len(&self.0) == 0
        }
        #[hax_lib::requires(index <= seq_len(&self.0))]
        fn insert(&mut self, index: usize, element: T) {
            let mut left = seq_slice(&self.0, 0, index);
            let right = seq_slice(&self.0, index, seq_len(&self.0));
            seq_concat(&mut left, &seq_one(element));
            seq_concat(&mut left, &right);
            self.0 = left;
        } 
        fn as_slice(&self) -> &[T] {
            seq_to_slice(&self.0)
        }
        #[hax_lib::opaque]
        fn truncate(&mut self, n: usize) {}
        #[hax_lib::opaque]
        fn swap_remove(&mut self, n: usize) -> T {seq_last(&self.0)}
        #[hax_lib::opaque]
        #[hax_lib::ensures(|_| future(self).len() == new_size)]
        fn resize(&mut self, new_size: usize, value: &T) {}
        #[hax_lib::opaque]
        fn remove(&mut self, index: usize) -> T {
            seq_last(&self.0)
        }
        #[hax_lib::opaque]
        fn clear(&mut self) {}
        #[hax_lib::requires(self.len().to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn append(&mut self, other: &mut Vec<T, A>) {
            seq_concat(&mut self.0, &other.0);
            other.0 = seq_empty()
        }
    }

    #[hax_lib::attributes]
    impl <T, A> Vec<T, A>  {
        #[hax_lib::requires(seq_len(&s.0).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(s: &mut Vec<T, A>, other: &[T]){
            seq_concat(&mut s.0, &seq_from_slice(other))
        }
    }
    

}
