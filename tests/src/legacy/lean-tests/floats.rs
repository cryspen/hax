// Tests on floats
#![allow(dead_code)]
#![allow(unused_variables)]

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): ssprove(HAX0001)
const N: f32 = 1.0;

/// @fail(extraction): ssprove(HAX0001)
fn test() {
    let l0 = 1.0;
    let l1 = 0.9;
    let l2 = 5.0f32;
    let l5 = N;
}

/// @fail(extraction): ssprove(HAX0001)
fn f(x: f64, y: f32) -> f32 {
    y
}
