// Tests on traits
#![allow(dead_code)]
#![allow(unused_variables)]

// Simple trait
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
