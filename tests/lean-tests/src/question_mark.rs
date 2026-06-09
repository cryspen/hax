//! Tests for the ? (question mark) operator
#![allow(dead_code)]
#![allow(unused_variables)]

// Basic ? on Option
fn option_basic(x: Option<u32>) -> Option<u32> {
    let v = x?;
    Some(v + 1)
}

// Multiple ? on Option
fn option_multi(x: Option<u32>, y: Option<u32>) -> Option<u32> {
    Some(x? + y?)
}

// ? on Option in conditional
fn option_in_if(x: Option<u32>) -> Option<u32> {
    let v = x?;
    if v > 10 { Some(v - 10) } else { Some(v) }
}

// Basic ? on Result
fn result_basic(x: Result<u32, &'static str>) -> Result<u32, &'static str> {
    let v = x?;
    Ok(v + 1)
}

// ? on Result with unit Ok
fn result_unit(x: Result<(), u32>) -> Result<i8, u32> {
    x?;
    Ok(0)
}

// Multiple ? on Result
fn result_multi(
    a: Result<u32, &'static str>,
    b: Result<u32, &'static str>,
) -> Result<u32, &'static str> {
    Ok(a? + b?)
}

// Chained ? with transformations
fn chained_transforms(x: Result<u32, &'static str>) -> Result<u32, &'static str> {
    let a = x?;
    let b = Ok::<u32, &'static str>(a + 1)?;
    let c = Ok::<u32, &'static str>(b * 2)?;
    Ok(c)
}

// Nested Result/Option with ?
fn nested_result_option(x: Result<Option<u32>, &'static str>) -> Result<u32, &'static str> {
    let opt = x?;
    match opt {
        Some(v) => Ok(v),
        None => Ok(0),
    }
}

// ? combined with struct construction
struct Pair {
    a: u32,
    b: u32,
}

fn construct_with_question_mark(x: Option<u32>, y: Option<u32>) -> Option<Pair> {
    Some(Pair { a: x?, b: y? })
}
