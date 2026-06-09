//! Tests on if-then-else
#![allow(dead_code)]
#![allow(unused_variables)]

// Basic if-then-else as expression
fn test1() -> i32 {
    let x = if true { 0 } else { 1 };
    if false { 2 } else { 3 }
}

// If-then-else with mutation
fn test2(b: bool) -> i32 {
    let x = if b { 0 } else { 9 };
    let mut y = 0;
    if true {
        y = y + x + 1
    } else {
        y = y - x - 1
    };
    if b {
        let z = y + y;
        z + y + x
    } else {
        let z = y - x;
        z + y + x
    }
}

// if-let with Option
fn if_let_option(x: Option<u32>) -> u32 {
    if let Some(v) = x { v + 1 } else { 0 }
}

// if-let with Result
fn if_let_result(x: Result<u32, i32>) -> u32 {
    if let Ok(v) = x { v * 2 } else { 0 }
}

// Chained if-let / else-if-let
fn chained_if_let(a: Option<u32>, b: Option<u32>) -> u32 {
    if let Some(x) = a {
        x
    } else if let Some(y) = b {
        y
    } else {
        0
    }
}

// if-let with tuple destructuring
fn if_let_tuple(x: Option<(u32, u32)>) -> u32 {
    if let Some((a, b)) = x { a + b } else { 0 }
}

// if-let with nested pattern
fn if_let_nested(x: Option<Option<u32>>) -> u32 {
    if let Some(Some(v)) = x { v } else { 0 }
}

// if-let with enum variant
enum Action {
    Move(i32, i32),
    Rotate(f32),
    Stop,
}

fn handle_move(a: Action) -> (i32, i32) {
    if let Action::Move(dx, dy) = a {
        (dx, dy)
    } else {
        (0, 0)
    }
}

// Deeply nested if-else
fn deeply_nested(a: bool, b: bool, c: bool) -> u32 {
    if a {
        if b {
            if c { 1 } else { 2 }
        } else {
            if c { 3 } else { 4 }
        }
    } else {
        if b {
            if c { 5 } else { 6 }
        } else {
            if c { 7 } else { 8 }
        }
    }
}

// if-else as argument to function
fn use_as_arg(b: bool) -> u32 {
    let f = |x: u32| x + 1;
    f(if b { 10 } else { 20 })
}

// if returning unit (statement-like)
fn if_unit(b: bool) -> u32 {
    let mut x = 0;
    if b {
        x = 1;
    }
    if !b {
        x = 2;
    }
    x
}

// Chained else-if (not if-let)
fn chained_else_if(x: u32) -> &'static str {
    if x == 0 {
        "zero"
    } else if x == 1 {
        "one"
    } else if x < 10 {
        "small"
    } else if x < 100 {
        "medium"
    } else {
        "large"
    }
}

// if-let with struct
struct Config {
    value: u32,
}

enum Setting {
    On(Config),
    Off,
}

fn read_config(s: Setting) -> u32 {
    if let Setting::On(Config { value }) = s {
        value
    } else {
        0
    }
}

// if in loop
fn if_in_loop(n: u32) -> u32 {
    let mut count = 0u32;
    let mut i = 0u32;
    while i < n {
        if i % 2 == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
