#![allow(dead_code)]

const FORTYTWO: usize = 42;
const MINUS_FORTYTWO: isize = -42;

fn returns42() -> usize {
    FORTYTWO
}

fn add_two_numbers(x: usize, y: usize) -> usize {
    x + y
}

fn letBinding(x: usize, y: usize) -> usize {
    let useless = ();
    let result1 = x + y;
    let result2 = result1 + 2;
    result2 + 1
}

fn closure() -> i32 {
    let x = 41;
    let f1 = |y| y + x;
    let f2 = |y, z| y + x + z;
    f1(1) + f2(2, 3)
}

#[hax_lib::lean::before("@[spec]")]
fn test_before_verbatime_single_line(x: u8) -> u8 {
    42
}

#[hax_lib::lean::before(
    "
def multiline : Unit := ()

"
)]
fn test_before_verbatim_multi_line(x: u8) -> u8 {
    32
}
