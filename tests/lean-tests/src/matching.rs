//! Tests on pattern matching
#![allow(dead_code)]
#![allow(unused_variables)]

// Matching on constants
fn test_const_matching(x: u32, c: char, s: &str, b: bool) -> u32 {
    let x = match x {
        0 => 42,
        _ => 0,
    };
    let c = match c {
        'a' => 42,
        _ => 0,
    };
    let s = match s {
        "Hello" => 42,
        _ => 0,
    };
    let b = match b {
        true => 42,
        false => 0,
    };
    return x + c + s + b;
}

// Binding subpattern with @
fn test_binding_subpattern_matching(x: (u8, (u8, u8))) -> u8 {
    match x {
        (0, pair @ (a, b)) => a + b + pair.0 + pair.1,
        _ => 0,
    }
}

// Ellipsis (..) in record/struct-variant patterns: all fields, some fields, no fields
fn test_ellipsis_records() {
    enum E {
        C { f1: u8, f2: u8, f3: u8, f4: u8 },
    }

    let c = E::C {
        f1: 1,
        f2: 2,
        f3: 3,
        f4: 4,
    };

    match c {
        E::C { .. } => assert!(true),
    };
    match c {
        E::C { f1, .. } => assert!(f1 == 1),
    };
    match c {
        E::C { f1, f2, .. } => assert!(f1 == 1 && f2 == 2),
    };
    match c {
        E::C { f2, f4, .. } => assert!(f2 == 2 && f4 == 4),
    };
    match c {
        E::C { f1, f2, f3, f4 } => assert!(f1 == 1 && f2 == 2 && f3 == 3 && f4 == 4),
    };
}

// Ellipsis (..) in plain struct patterns
fn test_ellipsis_structs() {
    struct S {
        f1: u8,
        f2: u8,
        f3: u8,
        f4: u8,
    }

    let c = S {
        f1: 1,
        f2: 2,
        f3: 3,
        f4: 4,
    };

    match c {
        S { .. } => assert!(true),
    };
    match c {
        S { f1, .. } => assert!(f1 == 1),
    };
    match c {
        S { f1, f2, .. } => assert!(f1 == 1 && f2 == 2),
    };
    match c {
        S { f2, f4, .. } => assert!(f2 == 2 && f4 == 4),
    };
    match c {
        S { f1, f2, f3, f4 } => assert!(f1 == 1 && f2 == 2 && f3 == 3 && f4 == 4),
    };
}

// Ellipsis (..) in bare tuple patterns: prefix, suffix, both ends
fn test_ellipsis_bare_tuples() {
    let t = (1u8, 2u8, 3u8, 4u8);

    match t {
        (..) => assert!(true),
    };
    match t {
        (a, ..) => assert!(a == 1),
    };
    match t {
        (a, b, ..) => assert!(a == 1 && b == 2),
    };
    match t {
        (.., d) => assert!(d == 4),
    };
    match t {
        (.., c, d) => assert!(c == 3 && d == 4),
    };
    match t {
        (a, .., d) => assert!(a == 1 && d == 4),
    };
    match t {
        (a, b, c, d) => assert!(a == 1 && b == 2 && c == 3 && d == 4),
    };
}

// Ellipsis (..) in enum tuple-variant patterns
fn test_ellipsis_tuples() {
    enum F {
        D(u8, u8, u8, u8),
    }

    let d = F::D(1, 2, 3, 4);

    match d {
        F::D(..) => assert!(true),
    };
    match d {
        F::D(a, ..) => assert!(a == 1),
    };
    match d {
        F::D(a, b, ..) => assert!(a == 1 && b == 2),
    };
    match d {
        F::D(.., d) => assert!(d == 4),
    };
    match d {
        F::D(.., c, d) => assert!(c == 3 && d == 4),
    };
    match d {
        F::D(a, .., d) => assert!(a == 1 && d == 4),
    };
    match d {
        F::D(a, b, c, d) => assert!(a == 1 && b == 2 && c == 3 && d == 4),
    };
}

// Nested tuple destructuring
fn nested_tuple_match(x: ((u32, u32), (u32, u32))) -> u32 {
    match x {
        ((a, b), (c, d)) => a + b + c + d,
    }
}

// Match with multiple arms and fallthrough wildcard
fn multi_arm(x: u32) -> u32 {
    match x {
        0 => 100,
        1 => 200,
        2 => 300,
        3 => 400,
        _ => 0,
    }
}

// Match returning different types from each arm (all same type)
fn match_expressions(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v * 2,
        None => 0,
    }
}

// Match on nested enums
enum Wrapper {
    Single(u32),
    Pair(u32, u32),
    Empty,
}

fn match_wrapper(w: Wrapper) -> u32 {
    match w {
        Wrapper::Single(x) => x,
        Wrapper::Pair(x, y) => x + y,
        Wrapper::Empty => 0,
    }
}

// Match on nested Options
fn match_nested_option(x: Option<Option<u32>>) -> u32 {
    match x {
        Some(Some(v)) => v,
        Some(None) => 1,
        None => 2,
    }
}

// Match on Result
fn match_result(x: Result<u32, i32>) -> u32 {
    match x {
        Ok(v) => v,
        Err(_) => 0,
    }
}

// Exhaustive matching on bool
fn match_bool_exhaustive(b: bool) -> u32 {
    match b {
        true => 1,
        false => 0,
    }
}

// Match on tuple of enums
fn match_enum_pair(a: Option<u32>, b: Option<u32>) -> u32 {
    match (a, b) {
        (Some(x), Some(y)) => x + y,
        (Some(x), None) => x,
        (None, Some(y)) => y,
        (None, None) => 0,
    }
}

// Deeply nested pattern
fn deep_pattern(x: Option<Result<(u32, u32), u32>>) -> u32 {
    match x {
        Some(Ok((a, b))) => a + b,
        Some(Err(e)) => e,
        None => 0,
    }
}

// Match with binding and computation in arm
fn match_with_block(x: Option<u32>) -> u32 {
    match x {
        Some(v) => {
            let doubled = v * 2;
            let tripled = v * 3;
            doubled + tripled
        }
        None => {
            let default = 42;
            default
        }
    }
}

// Multiple let-destructurings
fn multiple_let_destruct() -> u32 {
    let (a, b) = (1u32, 2u32);
    let (c, (d, e)) = (3u32, (4u32, 5u32));
    a + b + c + d + e
}

// Match with @ binding on enum
fn at_binding_enum(x: Option<u32>) -> u32 {
    match x {
        v @ Some(42) => 100,
        Some(n) => n,
        None => 0,
    }
}

// Match on reference
fn match_on_ref(x: &u32) -> u32 {
    match x {
        &0 => 100,
        &1 => 200,
        _ => 0,
    }
}

// Match returning unit
fn match_unit(x: u32) {
    match x {
        0 => (),
        _ => (),
    }
}

// Matching on ranges (inclusive)
fn match_range(x: u32) -> &'static str {
    match x {
        0..=9 => "digit",
        10..=99 => "two-digit",
        100..=999 => "three-digit",
        _ => "large",
    }
}

// Matching on char ranges
fn char_class(c: char) -> u32 {
    match c {
        'a'..='z' => 1,
        'A'..='Z' => 2,
        '0'..='9' => 3,
        _ => 0,
    }
}
