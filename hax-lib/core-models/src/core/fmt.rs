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

pub struct Arguments;

impl<T> Debug for T {
    fn dbg_fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
}

mod rt {
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
        fn new_display<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        fn new_debug<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
    }
    impl Argument<'_> {
        fn new_binary<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        fn new_lower_hex<T>(x: &T) -> Self {
            crate::panicking::internal::panic()
        }
        fn new_const<T, U>(x: &T, y: &U) -> super::Arguments {
            crate::panicking::internal::panic()
        }
        fn new_v1<T, U, V, W>(x: &T, y: &U, z: &V, t: &W) -> super::Arguments {
            crate::panicking::internal::panic()
        }
        fn none() -> [Self; 0] {
            []
        }
    }

    // Empty impls are needed to ensure the disambiguators are the same as in core
    impl Argument<'_> {}
    impl Argument<'_> {}

    impl<'a> Argument<'a> {
        fn new_v1_formatted<T>(x: &T) -> Self {
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
