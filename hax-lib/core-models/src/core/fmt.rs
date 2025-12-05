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

pub struct Arguments<'a>(&'a ());

impl<T> Debug for T {
    fn dbg_fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
}

impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {}
impl<'a> Arguments<'a> {
    fn write_fmt(f: &mut Formatter, args: Arguments) -> Result {
        Result::Ok(())
    }
}

mod rt {
    #[hax_lib::fstar::before(
        "open Rust_primitives.Arrays
open Rust_primitives.Integers"
    )]
    #[hax_lib::opaque]
    // The internals of this are not important in this model
    enum ArgumentType<'a> {
        Placeholder {
            /* value: NonNull<()>,
            formatter: unsafe fn(NonNull<()>, &mut Formatter<'_>) -> Result, */
            _lifetime: std::marker::PhantomData<&'a ()>,
        },
        /* Count(u16), */
    }

    pub struct Argument<'a> {
        ty: ArgumentType<'a>,
    }

    impl Argument<'_> {
        #[hax_lib::opaque]
        fn new_display<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        #[hax_lib::opaque]
        fn new_debug<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        #[hax_lib::opaque]
        fn new_lower_hex<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
    }
    impl<'a> Argument<'a> {
        #[hax_lib::opaque]
        fn new_binary<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        #[hax_lib::opaque]
        fn new_const<T, U>(x: &T, y: &U) -> super::Arguments<'a> {
            crate::panicking::internal::panic()
        }
        #[hax_lib::opaque]
        fn new_v1<T, U, V, W>(x: &T, y: &U, z: &V, t: &W) -> super::Arguments<'a> {
            crate::panicking::internal::panic()
        }
        fn none() -> [Self; 0] {
            []
        }
        #[hax_lib::opaque]
        fn new_v1_formatted<T, U, V>(x: &T, y: &U, z: &V) -> super::Arguments<'a> {
            crate::panicking::internal::panic()
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
