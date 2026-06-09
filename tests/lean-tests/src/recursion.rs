//! Tests on recursion
#![allow(dead_code)]
#![allow(unused_variables)]

// Simple recursion (non-tail)
fn factorial(n: u32) -> u32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}
