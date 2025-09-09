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
    // 2. Expressions
    let e_v1 = E::V1;
    let e_v2 = E::V2;
    let e_v3 = E::V3(23);
    let e_v4 = E::V4(23, 12, 1);
    let e_v5 = E::V5 { f1: 23, f2: 43 };
    let e_v6 = E::V6 { f1: 12, f2: 13 };
    let nil: MyList<usize> = MyList::Nil;
    let cons_1 = MyList::Cons {
        hd: 1,
        tl: Box::new(nil),
    };
    let cons_2_1 = MyList::Cons {
        hd: 2,
        tl: Box::new(cons_1),
    };

    // 3. Pattern matching
    match e_v1 {
        E::V1 => (),
        E::V2 => (),
        E::V3(_) => (),
        E::V4(x1, x2, x3) => {
            let y1 = x1 + x2;
            let y2 = y1 - x2;
            let y3 = y2 + x3;
            ()
        }
        E::V5 { f1, f2 } => (),
        E::V6 {
            f1,
            f2: other_name_for_f2,
        } => (),
    }
}
