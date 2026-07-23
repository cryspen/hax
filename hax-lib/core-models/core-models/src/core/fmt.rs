#![allow(unused_variables)]

/// See [`std::fmt::Error`]
pub struct Error;

/// See [`std::fmt::Result`]
pub type Result = super::result::Result<(), Error>;

/// See [`std::fmt::Formatter`]
pub struct Formatter;

impl Formatter {
    pub fn write_str(&mut self, data: &str) -> Result {
        Result::Ok(())
    }
}

/// See [`std::fmt::Display`]
pub trait Display {
    /// See [`std::fmt::Display::fmt`]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// See [`std::fmt::Debug`]
pub trait Debug {
    /// See [`std::fmt::Debug::fmt`]
    #[cfg(not(hax_backend_fstar))]
    fn fmt(&self, f: &mut Formatter) -> Result;
    #[cfg(hax_backend_fstar)]
    fn dbg_fmt(&self, f: &mut Formatter) -> Result;
}

/// See [`std::fmt::Arguments`]
pub struct Arguments<'a>(&'a ());

impl<T> Debug for T {
    #[cfg(not(hax_backend_fstar))]
    fn fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
    #[cfg(hax_backend_fstar)]
    fn dbg_fmt(&self, f: &mut Formatter) -> Result {
        Result::Ok(())
    }
}

// No blanket `Display` (unlike `Debug` above); spell out the integer impls,
// stubbed to `Ok(())` like the rest of this module.
macro_rules! impl_display_for_int {
    ($($t:ty),*) => {
        $(
            impl Display for $t {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    Result::Ok(())
                }
            }
        )*
    };
}

impl_display_for_int!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

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
