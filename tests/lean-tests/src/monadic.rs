//! Tests on monadic encoding
#![allow(dead_code)]
#![allow(unused_variables)]

fn test() {
    let _ = 9;
    let _ = 9 + 9;
    let _ = if true { 3 + 4 } else { 3 - 4 };
    let _ = if true {
        let x = 9;
        3 + x;
    } else {
        let y = 19;
        3 + y - 4;
    };
}
