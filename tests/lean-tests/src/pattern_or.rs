//! Tests for OR patterns in match expressions
#![allow(dead_code)]
#![allow(unused_variables)]

enum Color {
    Red,
    Green,
    Blue,
    Yellow,
    Cyan,
}

// Simple OR pattern on enum variants
fn simple_or(c: Color) -> u32 {
    match c {
        Color::Red | Color::Green => 1,
        Color::Blue | Color::Yellow | Color::Cyan => 2,
    }
}

// OR pattern on integers
fn int_or(x: u32) -> u32 {
    match x {
        0 | 1 => 10,
        2 | 3 | 4 => 20,
        _ => 30,
    }
}

// Nested OR inside Option
fn nested_option(x: Option<i32>) -> i32 {
    match x {
        Some(1 | 2) => 1,
        Some(3 | 4 | 5) => 2,
        Some(x) => x,
        None => 0,
    }
}

// Deep OR with tuples
fn deep_tuple(x: (i32, Option<i32>)) -> i32 {
    match x {
        (1 | 2, Some(3 | 4)) => 0,
        (5 | 6, None) => 1,
        (x, _) => x,
    }
}

// OR pattern with variable capture across Result branches
fn capture_across_or(x: Result<(i32, i32), (i32, i32)>) -> i32 {
    match x {
        Ok((1 | 2, y)) | Err((3 | 4, y)) => y,
        Ok((x, _)) | Err((x, _)) => x,
    }
}

// OR pattern in let destructuring
fn let_or(x: (u8, u8)) -> u8 {
    let (a, b) = x;
    a + b
}

// OR pattern on chars
fn char_or(c: char) -> u32 {
    match c {
        'a' | 'e' | 'i' | 'o' | 'u' => 1,
        'A' | 'E' | 'I' | 'O' | 'U' => 2,
        _ => 0,
    }
}

// OR pattern on booleans
fn bool_or(x: bool, y: bool) -> u32 {
    match (x, y) {
        (true, true) | (false, false) => 1,
        (true, false) | (false, true) => 2,
    }
}

// OR in nested enum
enum Outer {
    A(Inner),
    B(Inner),
}

enum Inner {
    X,
    Y(u32),
}

fn nested_enum_or(o: Outer) -> u32 {
    match o {
        Outer::A(Inner::X) | Outer::B(Inner::X) => 0,
        Outer::A(Inner::Y(v)) | Outer::B(Inner::Y(v)) => v,
    }
}

// OR combined with wildcard
fn or_with_wildcard(x: (u32, u32, u32)) -> u32 {
    match x {
        (0 | 1, _, z) => z,
        (_, 0 | 1, z) => z + 1,
        (_, _, z) => z + 2,
    }
}

// OR in if-let (refutable pattern)
fn or_in_if_let(x: Option<u32>) -> u32 {
    if let Some(1 | 2 | 3) = x { 42 } else { 0 }
}
