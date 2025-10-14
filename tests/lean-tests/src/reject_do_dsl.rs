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
