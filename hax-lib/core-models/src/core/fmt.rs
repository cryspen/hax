#![allow(unused_variables)]

pub struct Error;

pub type Result = super::result::Result<(), Error>;

pub struct Formatter;

pub trait Display {
    fn fmt(&self, f: &mut Formatter) -> Result;
}

pub trait Debug {
    fn dbg_fmt(&self, f: &mut Formatter) -> Result;
}

pub type Arguments = rt::Argument;

impl<T> Debug for T {
    fn dbg_fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
}

mod rt {
    #[hax_lib::fstar::before("open Rust_primitives.Arrays")]
    pub struct Argument;
    impl Argument {
        fn new_display<T>(x: &T) -> Argument {
            Argument
        }
        fn new_debug<T>(x: &T) -> Argument {
            Argument
        }
        fn new_v1_formatted<T>(x: &T) -> Argument {
            Argument
        }
        fn new_binary<T>(x: &T) -> Argument {
            Argument
        }
        fn new_lower_hex<T>(x: &T) -> Argument {
            Argument
        }
        fn new_const<T, U>(x: &T, y: &U) -> Argument {
            Argument
        }
        fn new_v1<T, U, V, W>(x: &T, y: &U, z: &V, t: &W) -> Argument {
            Argument
        }
        fn none() -> [Argument; 0] {
            []
        }
    }

    enum Count {
        Is(u16),
        Param(u16),
        Implied,
    }

    struct Placeholder {
        position: usize,
        flags: u32,
        precision: Count,
        width: Count,
    }

    struct UnsafeArg;
}
