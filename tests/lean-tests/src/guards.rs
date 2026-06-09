//! Tests for match guards
#![allow(dead_code)]
#![allow(unused_variables)]

// Basic if guard with boolean condition
fn simple_if_guard(x: Option<i32>) -> i32 {
    match x {
        Some(v) if v > 0 => v,
        Some(v) if v < -10 => -v,
        Some(_) => 0,
        None => -1,
    }
}

// Guard referencing outer variable
fn guard_with_outer(x: Option<i32>, threshold: i32) -> i32 {
    match x {
        Some(v) if v > threshold => v - threshold,
        Some(v) => v,
        None => 0,
    }
}

// Guard on enum variants
enum Shape {
    Circle(u32),
    Rect(u32, u32),
    Square(u32),
}

fn area_filter(s: Shape, min_area: u32) -> bool {
    match s {
        Shape::Circle(r) if r * r > min_area => true,
        Shape::Rect(w, h) if w * h > min_area => true,
        Shape::Square(s) if s * s > min_area => true,
        _ => false,
    }
}

// Guard on nested option
fn nested_option_guard(x: Option<Option<i32>>) -> i32 {
    match x {
        Some(Some(v)) if v > 0 => v,
        Some(Some(v)) => -v,
        Some(None) => -1,
        None => -2,
    }
}
