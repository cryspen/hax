//! Tests for let-else statements
#![allow(dead_code)]
#![allow(unused_variables)]

// Basic let-else with Option
fn basic_option(opt: Option<u32>) -> u32 {
    let Some(x) = opt else { return 0 };
    x + 1
}

// let-else with Result
fn basic_result(res: Result<u32, i32>) -> u32 {
    let Ok(x) = res else { return 0 };
    x + 1
}

// Multiple let-else in sequence
fn chained(a: Option<u32>, b: Option<u32>) -> u32 {
    let Some(x) = a else { return 0 };
    let Some(y) = b else { return x };
    x + y
}

// let-else with tuple destructuring
fn tuple_destructure(opt: Option<(u32, u32)>) -> u32 {
    let Some((a, b)) = opt else { return 0 };
    a + b
}

// let-else with struct pattern
struct Point {
    x: i32,
    y: i32,
}

enum Geom {
    Pt(Point),
    Nothing,
}

fn struct_let_else(g: Geom) -> i32 {
    let Geom::Pt(Point { x, y }) = g else {
        return -1;
    };
    x + y
}

// let-else with nested Option
fn nested_option(opt: Option<Option<u32>>) -> u32 {
    let Some(inner) = opt else { return 0 };
    let Some(v) = inner else { return 1 };
    v + 2
}

// let-else returning different divergent expressions
fn with_early_return_result(opt: Option<u32>) -> Result<u32, &'static str> {
    let Some(x) = opt else {
        return Err("missing");
    };
    Ok(x * 2)
}

// let-else with enum variant
enum Token {
    Number(u32),
    Plus,
    Minus,
    Eof,
}

fn extract_number(t: Token) -> Option<u32> {
    let Token::Number(n) = t else { return None };
    Some(n)
}
