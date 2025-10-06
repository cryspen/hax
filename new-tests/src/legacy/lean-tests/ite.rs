//! Tests on if-then-else
#![allow(dead_code)]
#![allow(unused_variables)]

fn test1() -> i32 {
    let x = if true { 0 } else { 1 };
    if false {
        2
    } else {
        3
    }
}

fn test2(b: bool) -> i32 {
    let x = if b { 0 } else { 9 };
    let mut y = 0;
    if true {
        y = y + x + 1
    } else {
        y = y - x - 1
    };
    if b {
        let z = y + y;
        z + y + x
    } else {
        let z = y - x;
        z + y + x
    }
}
