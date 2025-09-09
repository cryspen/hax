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
        fn f_test(&self, x: T) -> usize;
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
        fn f_test(&self, x: S1) -> usize {
            x.f1() + self.f2() + 1
        }
    }
}
