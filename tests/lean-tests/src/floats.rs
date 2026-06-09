//! Tests on floats
#![allow(dead_code)]
#![allow(unused_variables)]

// Float constants
const N: f32 = 1.0;
const PI_F32: f32 = 3.14159;
const PI_F64: f64 = 3.141592653589793;
const NEG_ONE: f64 = -1.0;

// Basic float literals
fn float_literals() {
    let _l0 = 1.0;
    let _l1 = 0.9;
    let _l2 = 5.0f32;
    let _l3 = N;
    let _l4 = 0.0f64;
    let _l5 = -3.14;
    let _l6 = 1.0e10;
    let _l7 = 2.5E-3;
    let _l8 = 100.0f64;
}

// Float as function args and return
fn f(x: f64, y: f32) -> f32 {
    y
}
// Float in tuple
fn float_tuple() -> (f32, f64) {
    (1.5f32, 2.5f64)
}

// Float in array
fn float_array() -> [f64; 3] {
    [1.0, 2.0, 3.0]
}
