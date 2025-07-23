#![allow(dead_code)]

const FORTYTWO: usize = 42;

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
    let f = |y| y + x;
    f(1)
}

type UsizeAlias = usize;

// Hello world example from https://hacspec.zulipchat.com/#narrow/channel/269544-general/topic/hax.20.2B.20coq/with/528801096
fn main() {
    let x = square(10u8);
    println!("{}", x);
}

#[hax_lib::requires(n < 16u8)]
fn square(n: u8) -> u8 {
    n * n
}
