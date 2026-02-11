//! Tests on loops
#![allow(dead_code)]
#![allow(unused_variables)]

// Simple loop
fn loop1() -> u32 {
    let mut x: u32 = 0;
    for i in 1..10 {
        x = x + i
    }
    x
}

// Loop with a return
fn loop2() -> u32 {
    let mut x: u32 = 0;
    for i in 1..10 {
        if i == 5 {
            return x;
        }
        x = x + i;
    }
    x
}

#[hax_lib::ensures(|r| r == 0)]
#[hax_lib::lean::proof_method("grind")]
fn while_loop1(s: u32) -> u32 {
    let mut x: u32 = s;
    while x > 0 {
        hax_lib::loop_decreases!(x);
        x = x - 1;
    }
    x
}

mod errors {
    enum Error {
        Foo,
        Bar(u32),
    }

    fn loop3() -> Result<u32, Error> {
        let mut x = 0;
        let end: u32 = 10;
        for i in 1..end {
            if i == 5 {
                return Err(Error::Foo);
            }
            x = x + 5
        }
        Ok(x)
    }

    fn loop4() -> Result<(u32, u32), Error> {
        let mut e = 0;
        let f = |()| 42;

        for i in 0..(f(())) {
            // verify degree bound
            if i > 10 {
                return Err(Error::Bar(e));
            }
            e = e + i
        }

        Ok((e, e))
    }
}
