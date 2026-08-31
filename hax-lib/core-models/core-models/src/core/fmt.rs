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
    // F*-only: `charon::opaque` drops the declaration too, and `Argument`'s
    // field still names this type, so Lean would not elaborate.
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
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

    // The formatting arguments carry no observable payload in this model, so
    // every constructor below yields the single placeholder value. Opaque like
    // `ArgumentType` itself: charon drops that enum's variants, so a body
    // building one would leave aeneas without the fields.
    #[hax_lib::opaque]
    fn placeholder<'a>() -> ArgumentType<'a> {
        ArgumentType::Placeholder {
            _lifetime: std::marker::PhantomData,
        }
    }

    impl Argument<'_> {
        #[hax_lib::opaque]
        fn new_display<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_debug<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_lower_hex<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
    }
    impl<'a> Argument<'a> {
        #[hax_lib::opaque]
        fn new_binary<T>(x: &T) -> Self {
            Argument { ty: placeholder() }
        }
        #[hax_lib::opaque]
        fn new_const<T, U>(x: &T, y: &U) -> super::Arguments<'a> {
            super::Arguments(&())
        }
        #[hax_lib::opaque]
        fn new_v1<T, U, V, W>(x: &T, y: &U, z: &V, t: &W) -> super::Arguments<'a> {
            super::Arguments(&())
        }
        fn none() -> [Self; 0] {
            []
        }
        #[hax_lib::opaque]
        fn new_v1_formatted<T, U, V>(x: &T, y: &U, z: &V) -> super::Arguments<'a> {
            super::Arguments(&())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{Argument, ArgumentType};

        /// The `rt` constructors are placeholders (core's real ones build
        /// type-erased trait objects), so all a test can check is that each one
        /// returns the placeholder rather than diverging.
        fn is_placeholder(a: &Argument<'_>) -> bool {
            matches!(a.ty, ArgumentType::Placeholder { .. })
        }

        #[test]
        fn test_argument_constructors() {
            assert!(is_placeholder(&Argument::new_display(&1u8)));
            assert!(is_placeholder(&Argument::new_debug(&1u8)));
            assert!(is_placeholder(&Argument::new_lower_hex(&1u8)));
            assert!(is_placeholder(&Argument::new_binary(&1u8)));
            assert!(Argument::none().is_empty());
        }

        #[test]
        fn test_arguments_constructors() {
            // `Arguments` has no observable content either; construction is all
            // there is to check.
            let _ = Argument::new_const(&1u8, &2u8);
            let _ = Argument::new_v1(&1u8, &2u8, &3u8, &4u8);
            let _ = Argument::new_v1_formatted(&1u8, &2u8, &3u8);
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

#[cfg(test)]
mod tests {
    use super::{Arguments, Display, Formatter, Result};

    // Everything in this module is a stub returning `Ok(())`: the model has no
    // output buffer, so `Ok(())` is the whole observable behaviour.
    // `fmt::Error` has no `PartialEq`, hence `is_ok` rather than `assert_eq!`.
    #[test]
    fn test_write_str() {
        let mut f = Formatter;
        assert!(f.write_str("hello").is_ok());
    }

    #[test]
    fn test_debug_fmt() {
        let mut f = Formatter;
        #[cfg(not(hax_backend_fstar))]
        assert!(super::Debug::fmt(&1u8, &mut f).is_ok());
        #[cfg(hax_backend_fstar)]
        assert!(super::Debug::dbg_fmt(&1u8, &mut f).is_ok());
    }

    macro_rules! display_tests {
        ($($t:ident),*) => {
            pastey::paste! { $(
                #[test]
                fn [<test_display_ $t>]() {
                    let mut f = Formatter;
                    assert!(Display::fmt(&(0 as $t), &mut f).is_ok());
                }
            )* }
        };
    }

    display_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    #[test]
    fn test_write_fmt() {
        let mut f = Formatter;
        assert!(Arguments::write_fmt(&mut f, Arguments(&())).is_ok());
    }

    // `Arguments` can only be built inside this module, so `panicking::panic_fmt`
    // is exercised here rather than next to the other `panicking` tests.
    #[test]
    #[should_panic]
    fn test_panic_fmt() {
        crate::panicking::panic_fmt(Arguments(&()));
    }
}
