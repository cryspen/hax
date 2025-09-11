// Tests on traits
#![allow(dead_code)]
#![allow(unused_variables)]

// Simple trait
mod basic {
    trait T1 {
        fn f1(&self) -> usize;
        fn f2(&self, other: &Self) -> usize;
    }

    // Simple Impl
    struct S;

    impl T1 for S {
        fn f1(&self) -> usize {
            42
        }

        fn f2(&self, other: &Self) -> usize {
            43
        }
    }

    // Simple ImplExpr
    fn f<T: T1>(x: T) -> usize {
        x.f1() + x.f2(&x)
    }
}

// Bounds on parameters and on self
mod bounds {
    trait T1 {
        fn f1(&self) -> usize;
    }
    trait T2 {
        fn f2(&self) -> usize;
    }

    trait Test<T: T1>: T2 {
        fn f_test(&self, x: &T) -> usize;
    }

    struct S1;
    impl T1 for S1 {
        fn f1(&self) -> usize {
            0
        }
    }

    struct S2;
    impl T2 for S2 {
        fn f2(&self) -> usize {
            1
        }
    }

    impl Test<S1> for S2 {
        fn f_test(&self, x: &S1) -> usize {
            x.f1() + self.f2() + 1
        }
    }

    fn test(x1: S1, x2: S2) -> usize {
        x2.f_test(&x1) + x1.f1()
    }
}

mod associated_types {
    trait T1 {
        type T;
        fn f(&self, x: Self::T) -> Self::T;
    }

    trait T2 {
        type T: T1;
        fn f(&self, x: Self::T) -> usize;
    }

    trait Foo<T> {}
    trait Bar {}

    trait T3 {
        type T: Foo<()>;
        type Tp<T: Bar>: Foo<T>;
        fn f<A: Bar>(&self, x: Self::T, y: Self::Tp<A>) -> usize;
    }
}

mod overlapping_methods {

    trait T1 {
        fn f(&self) -> usize;
    }
    trait T2 {
        fn f(&self) -> usize;
    }
    trait T3 {
        fn f(&self) -> usize;
    }
    impl T1 for u32 {
        fn f(&self) -> usize {
            0
        }
    }
    impl T2 for u32 {
        fn f(&self) -> usize {
            1
        }
    }
    impl T3 for u32 {
        fn f(&self) -> usize {
            2
        }
    }
    fn test() -> usize {
        let x: u32 = 9;
        T1::f(&x) + T2::f(&x) + T3::f(&x)
    }
}
