//! Tests on patterns rejected by the engine as outside of Lean's do-notation DSL
#![allow(dead_code)]
#![allow(unused_variables)]

fn rejected() {
    let x1 = 1 + (if true { 0 } else { 1 });
    let x2 = 1
        + (match (1, 2) {
            _ => 0,
        });
    let x3 = 1 + {
        let x = 9;
        x + 1
    };
}

/// Code that should be produced from the rejected code
fn accepted() {
    let x1_tmp = if true { 0 } else { 1 };
    let x1 = 1 + x1_tmp;
    let x2_tmp = match (1, 2) {
        _ => 0,
    };
    let x2 = 1 + x2_tmp;
    let x3_tmp_x = 9;
    let x3_tmp = x3_tmp_x + 1;
    let x3 = 1 + x3_tmp;
}

// Other cases that should be accepted
fn test() {
    let mut x1 = if true {
        let mut y = if false {
            let mut z = match () {
                _ => 9,
            };
            z = 1 + z;
            z + 1
        } else {
            let mut z = 9;
            z = z + 1;
            z
        };
        y = y + 1;
        y + 1
    } else {
        0
    };
    x1 = x1 + 1;
    let mut x2 = match Some(89) {
        Some(a) => {
            let mut y = 1 + a;
            y = y + 1;
            if y == 0 {
                let mut z = 9;
                z = z + y + 1;
                z
            } else {
                10
            }
        }
        None => {
            let mut y = if false {
                9
            } else {
                let mut z = 9;
                z = z + 1;
                z + 9
            };
            y = y + 1;
            y
        }
    };
    x2 = x1 + 1 + x2
}
