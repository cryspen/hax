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
    struct Box<T>(T);
    impl <T> Box<T> {
        fn new(v: T) -> Box<T> {
            Box(v)
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
        pub type VecDeque<T, A> = rust_primitives::seq::Seq<T, A>;
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

    impl Dummy {
        fn to_vec<T>(s: &[T]) -> Vec<T, crate::alloc::Global> {
            rust_primitives::seq::seq_from_slice(s)
        }
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
    #[hax_lib::fstar::before("unfold type t_Vec t (_: unit) = t_Slice t")]
    use rust_primitives::seq::*;

    pub type Vec<T, A> = Seq<T, A>;

    // struct Vec<T, A>(Seq<T>, A);

    #[hax_lib::exclude]
    struct Dummy<T, A>(Option<T>, Option<A>);

    impl <T> Dummy<T, crate::alloc::Global> {
        fn new() -> Vec<T, crate::alloc::Global> {
            seq_empty()
        }
        fn with_capacity() -> Vec<T, crate::alloc::Global> {
            seq_empty()
        }
    }

    #[hax_lib::attributes]
    impl <T, A> Dummy<T, A> {
        fn len(v: &Vec<T, A>) -> usize {
            seq_len(v)
        }
        #[hax_lib::requires(seq_len(v) < usize::MAX)]
        fn push(v: &mut Vec<T, A>, x: T) {
            seq_concat(v, seq_one(x))
        } 
        fn pop(v: &mut Vec<T, A>) -> Option<T> {
            if seq_len(v) == 0 {
                None
            } else {
                *v = seq_slice(v, 0, seq_len(v) - 1);
                Some(seq_last(v))
            }
        }
        fn is_empty(v: &Vec<T, A>) -> bool {
            seq_len(v) == 0
        }
        #[hax_lib::requires(index <= seq_len(v))]
        fn insert(v: &mut Vec<T, A>, index: usize, element: T) {
            let mut left = seq_slice(v, 0, index);
            let right = seq_slice(v, index, seq_len(v));
            seq_concat(&mut left, seq_one(element));
            seq_concat(&mut left, right);
            *v = left;
        } 
    }

    use hax_lib::ToInt;
    #[hax_lib::attributes]
    impl <T, A> Dummy<T, A>  {
        #[hax_lib::requires(seq_len(s).to_int() + other.len().to_int() <= usize::MAX.to_int())]
        fn extend_from_slice(s: &mut Vec<T, A>, other: &[T]){
            seq_concat(s, seq_from_slice(other))
        }
    }
}
