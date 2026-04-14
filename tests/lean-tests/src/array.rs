//! Tests on arrays
#![allow(dead_code)]
#![allow(unused_variables)]

// Arrays with const generic sizes (existing)
fn f<const N: usize>(x: [u8; N]) {}

fn g<const N: usize>(x: [u8; N]) {
    f(x);
    f([0u8; 10]);
}
