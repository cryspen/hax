// Tests for core models in lean
#![allow(dead_code)]
#![allow(unused_variables)]

// Default on struct
mod structs {
    struct S {
        f1: usize,
    }

    impl Default for S {
        fn default() -> Self {
            S { f1: 0 }
        }
    }

    fn test() -> S {
        S::default()
    }
}

// Default on enum
mod enums {
    enum E<T> {
        C1(u32),
        C2(T),
    }

    impl<T: Default> Default for E<T> {
        fn default() -> Self {
            E::C2(T::default())
        }
    }
}
