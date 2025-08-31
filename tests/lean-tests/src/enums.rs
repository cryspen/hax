//! Tests on enums
#![allow(dead_code)]
#![allow(unused_variables)]

// 1. Type definition
enum E {
    // unit-like
    V1,
    V2,
    // with positional arguments
    V3(usize),
    V4(usize, usize, usize),
    // with named arguments
    V5 { f1: usize, f2: usize },
    V6 { f1: usize, f2: usize },
}

enum MyList<T> {
    Nil,
    Cons { hd: T, tl: Box<MyList<T>> },
}

fn enums() -> () {
    let e2_v1 = E::V1;
    let e2_v2 = E::V2;
    let nil: MyList<usize> = MyList::Nil;
}
