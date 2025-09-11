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
        type T: Bar;
        type Tp<A: Bar>: Foo<Self::T>;
        fn f<A: Bar>(&self, x: Self::T, y: Self::Tp<A>) -> usize;
    }

    struct S {}
    impl T1 for S {
        type T = i32;

        fn f(&self, x: Self::T) -> Self::T {
            2121
        }
    }
    impl T2 for S {
        type T = S;

        fn f(&self, x: Self::T) -> usize {
            21
        }
    }

    impl Bar for i16 {}
    impl<A> Foo<i16> for (u32, A) {}

    // impl T3 for S {
    //     type T = i16;

    //     type Tp<A: Bar> = (u32, A);

    //     fn f<A: Bar>(&self, x: Self::T, y: Self::Tp<A>) -> usize {
    //         12
    //     }
    // }
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

mod inheritance {
    trait T1 {
        fn f1(&self) -> usize;
    }
    trait T2 {
        fn f2(&self) -> usize;
    }
    trait T3: T2 + T1 {
        fn f3(&self) -> usize;
    }
    trait Tp1 {
        fn f1(&self) -> usize;
    }
    trait Tp2: Tp1 + T3 {
        fn fp2(&self) -> usize;
    }

    struct S {}
    impl T1 for S {
        fn f1(&self) -> usize {
            1
        }
    }
    impl T2 for S {
        fn f2(&self) -> usize {
            2
        }
    }
    impl T3 for S {
        fn f3(&self) -> usize {
            3
        }
    }

    impl Tp1 for S {
        fn f1(&self) -> usize {
            10
        }
    }

    impl Tp2 for S {
        fn fp2(&self) -> usize {
            Tp1::f1(self) + T1::f1(self) + T2::f2(self) + T3::f3(self)
        }
    }
    fn test() -> usize {
        let s = S {};
        s.f3() + 1
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
