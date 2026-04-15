//! Tests on arrays
#![allow(dead_code)]
#![allow(unused_variables)]

// Arrays with const generic sizes (existing)
fn f<const N: usize>(x: [u8; N]) {}

fn g<const N: usize>(x: [u8; N]) {
    f(x);
    f([0u8; 10]);
}

// Array literals
fn array_literals() {
    let _empty: [u32; 0] = [];
    let _one = [42u32];
    let _three = [1u32, 2, 3];
    let _five = [10u8, 20, 30, 40, 50];
    let _bools = [true, false, true];
    let _chars = ['a', 'b', 'c'];
}

// Array repeat syntax
fn array_repeat() {
    let _zeros = [0u32; 5];
    let _ones = [1u8; 10];
    let _falses = [false; 3];
}

// Array indexing
fn array_index(arr: [u32; 5]) -> u32 {
    let first = arr[0];
    let last = arr[4];
    first + last
}

// Array element access in expressions
fn array_in_expr(arr: [u32; 3]) -> u32 {
    arr[0] + arr[1] * arr[2]
}

// Array as function argument and return
fn sum_array_3(arr: [u32; 3]) -> u32 {
    arr[0] + arr[1] + arr[2]
}

fn make_array(a: u32, b: u32, c: u32) -> [u32; 3] {
    [a, b, c]
}

// Nested arrays
fn nested_arrays() {
    let _matrix: [[u32; 3]; 2] = [[1, 2, 3], [4, 5, 6]];
    let _access = _matrix[0][1];
    let _row = _matrix[1];
}

// Array of tuples
fn array_of_tuples() -> [(u32, u32); 3] {
    [(1, 2), (3, 4), (5, 6)]
}

// Array with const generic arithmetic
fn double_array<const N: usize>(a: [u32; N], b: [u32; N]) -> u32 {
    a[0] + b[0]
}

// Pattern matching on arrays
fn match_array(arr: [u32; 3]) -> u32 {
    let [a, b, c] = arr;
    a + b + c
}

fn match_array_nested(arr: [[u32; 2]; 2]) -> u32 {
    let [[a, b], [c, d]] = arr;
    a + b + c + d
}

// Array of structs
struct Point {
    x: u32,
    y: u32,
}

fn array_of_structs() -> [Point; 2] {
    [Point { x: 0, y: 1 }, Point { x: 2, y: 3 }]
}

// Passing array by reference
fn sum_ref(arr: &[u32; 4]) -> u32 {
    arr[0] + arr[1] + arr[2] + arr[3]
}

// Const generic size in struct
struct Buffer<const N: usize> {
    data: [u8; N],
}

fn make_buffer() -> Buffer<16> {
    Buffer { data: [0u8; 16] }
}
