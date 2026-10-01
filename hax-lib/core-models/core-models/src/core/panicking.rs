//! Model of `core::panicking`. Items are not doc-linked: it has no `std`
//! re-export.

// F*-only: `charon::opaque` drops the declaration too, and extracted bodies
// across the model call these, so Lean would not elaborate.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic_explicit() -> ! {
    panic!()
}

#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic(_msg: &str) -> ! {
    panic!()
}

#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::requires(false)]
pub fn panic_fmt(_fmt: super::fmt::Arguments) -> ! {
    panic!()
}

/// `core::panicking::AssertKind` — which of `assert_eq!` / `assert_ne!` /
/// `assert_matches!` failed. Carried by the `assert_failed` shims; the model
/// has no use for it beyond giving a client's mention of it a name.
pub enum AssertKind {
    /// `core::panicking::AssertKind::Eq`
    Eq,
    /// `core::panicking::AssertKind::Ne`
    Ne,
    /// `core::panicking::AssertKind::Match`
    Match,
}

/// `core::panicking::panic_nounwind`. Takes `&str`, not `&'static str`.
// Aeneas cannot translate an argument with an explicit `'static`.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_nounwind(_expr: &str) -> ! {
    panic!()
}

/// `core::panicking::panic_nounwind_nobacktrace`. Takes `&str`, not `&'static str`.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_nounwind_nobacktrace(_expr: &str) -> ! {
    panic!()
}

/// `core::panicking::panic_nounwind_fmt`
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_nounwind_fmt(_fmt: super::fmt::Arguments, _force_no_backtrace: bool) -> ! {
    panic!()
}

/// `core::panicking::const_panic_fmt`
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn const_panic_fmt(_fmt: super::fmt::Arguments) -> ! {
    panic!()
}

/// `core::panicking::panic_str_2015`
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_str_2015(_expr: &str) -> ! {
    panic!()
}

/// `core::panicking::panic_display`
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_display<T: super::fmt::Display>(_x: &T) -> ! {
    panic!()
}

/// `core::panicking::unreachable_display`
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn unreachable_display<T: super::fmt::Display>(_x: &T) -> ! {
    panic!()
}

/// `core::panicking::panic_const`
pub mod panic_const {
    macro_rules! panic_const {
        ($($name:ident = $message:literal,)+) => {
            $(
                #[doc = concat!("`core::panicking::panic_const::", stringify!($name),
                                "`; std's message is \"", $message, "\".")]
                #[hax_lib::opaque]
                #[hax_lib::requires(false)]
                pub fn $name() -> ! {
                    panic!($message)
                }
            )+
        };
    }

    panic_const! {
        panic_const_add_overflow = "attempt to add with overflow",
        panic_const_sub_overflow = "attempt to subtract with overflow",
        panic_const_mul_overflow = "attempt to multiply with overflow",
        panic_const_div_overflow = "attempt to divide with overflow",
        panic_const_rem_overflow = "attempt to calculate the remainder with overflow",
        panic_const_neg_overflow = "attempt to negate with overflow",
        panic_const_shr_overflow = "attempt to shift right with overflow",
        panic_const_shl_overflow = "attempt to shift left with overflow",
        panic_const_div_by_zero = "attempt to divide by zero",
        panic_const_rem_by_zero = "attempt to calculate the remainder with a divisor of zero",
        panic_const_coroutine_resumed = "coroutine resumed after completion",
        panic_const_async_fn_resumed = "`async fn` resumed after completion",
        panic_const_async_gen_fn_resumed = "`async gen fn` resumed after completion",
        panic_const_gen_fn_none = "`gen fn` should just keep returning `None` after completion",
        panic_const_coroutine_resumed_panic = "coroutine resumed after panicking",
        panic_const_async_fn_resumed_panic = "`async fn` resumed after panicking",
        panic_const_async_gen_fn_resumed_panic = "`async gen fn` resumed after panicking",
        panic_const_gen_fn_none_panic = "`gen fn` should just keep returning `None` after panicking",
        panic_const_coroutine_resumed_drop = "coroutine resumed after async drop",
        panic_const_async_fn_resumed_drop = "`async fn` resumed after async drop",
        panic_const_async_gen_fn_resumed_drop = "`async gen fn` resumed after async drop",
        panic_const_gen_fn_none_drop = "`gen fn` resumed after async drop",
    }
}

pub mod internal {
    // This module is used to break a dependency cycle (other core modules have
    // panics and this brings a dependency on core::fmt that we need to avoid)
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    #[hax_lib::requires(false)]
    pub fn panic<T>() -> T {
        panic!("")
    }
}

#[cfg(test)]
mod tests {
    use super::panic_const::*;
    use crate::testing::panics_like_core;
    use std::hint::black_box;

    // Compared against the operation that trips the assertion.
    #[test]
    fn test_panic_const_add_overflow() {
        panics_like_core(
            || panic_const_add_overflow(),
            || black_box(u8::MAX) + black_box(1u8),
        );
    }

    #[test]
    fn test_panic_const_sub_overflow() {
        panics_like_core(
            || panic_const_sub_overflow(),
            || black_box(0u8) - black_box(1u8),
        );
    }

    #[test]
    fn test_panic_const_mul_overflow() {
        panics_like_core(
            || panic_const_mul_overflow(),
            || black_box(u8::MAX) * black_box(2u8),
        );
    }

    #[test]
    fn test_panic_const_div_overflow() {
        panics_like_core(
            || panic_const_div_overflow(),
            || black_box(i8::MIN) / black_box(-1i8),
        );
    }

    #[test]
    fn test_panic_const_rem_overflow() {
        panics_like_core(
            || panic_const_rem_overflow(),
            || black_box(i8::MIN) % black_box(-1i8),
        );
    }

    #[test]
    fn test_panic_const_neg_overflow() {
        panics_like_core(|| panic_const_neg_overflow(), || -black_box(i8::MIN));
    }

    #[test]
    fn test_panic_const_shl_overflow() {
        panics_like_core(
            || panic_const_shl_overflow(),
            || black_box(1u8) << black_box(8u32),
        );
    }

    #[test]
    fn test_panic_const_shr_overflow() {
        panics_like_core(
            || panic_const_shr_overflow(),
            || black_box(1u8) >> black_box(8u32),
        );
    }

    #[test]
    fn test_panic_const_div_by_zero() {
        panics_like_core(
            || panic_const_div_by_zero(),
            || black_box(1u8) / black_box(0u8),
        );
    }

    #[test]
    fn test_panic_const_rem_by_zero() {
        panics_like_core(
            || panic_const_rem_by_zero(),
            || black_box(1u8) % black_box(0u8),
        );
    }

    // No stable Rust trips these, so only divergence is checked.
    macro_rules! diverges {
        ($($name:ident => $f:path;)*) => {
            $(
                #[test]
                #[should_panic]
                fn $name() {
                    $f();
                }
            )*
        };
    }

    diverges! {
        test_panic_const_coroutine_resumed => panic_const_coroutine_resumed;
        test_panic_const_coroutine_resumed_panic => panic_const_coroutine_resumed_panic;
        test_panic_const_coroutine_resumed_drop => panic_const_coroutine_resumed_drop;
        test_panic_const_async_fn_resumed => panic_const_async_fn_resumed;
        test_panic_const_async_fn_resumed_panic => panic_const_async_fn_resumed_panic;
        test_panic_const_async_fn_resumed_drop => panic_const_async_fn_resumed_drop;
        test_panic_const_async_gen_fn_resumed => panic_const_async_gen_fn_resumed;
        test_panic_const_async_gen_fn_resumed_panic => panic_const_async_gen_fn_resumed_panic;
        test_panic_const_async_gen_fn_resumed_drop => panic_const_async_gen_fn_resumed_drop;
        test_panic_const_gen_fn_none => panic_const_gen_fn_none;
        test_panic_const_gen_fn_none_panic => panic_const_gen_fn_none_panic;
        test_panic_const_gen_fn_none_drop => panic_const_gen_fn_none_drop;
    }

    #[test]
    fn test_panic_const_messages_match_core() {
        // Every payload below is a `&str`, so the `String` fallback is unreachable.
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn message_of(f: impl FnOnce()) -> String {
            let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).unwrap_err();
            match payload.downcast_ref::<&str>() {
                Some(s) => (*s).to_string(),
                None => payload
                    .downcast_ref::<String>()
                    .cloned()
                    .unwrap_or_default(),
            }
        }

        let cases: Vec<(fn() -> !, Box<dyn FnOnce()>)> = vec![
            (
                panic_const_add_overflow,
                Box::new(|| {
                    let _ = black_box(u8::MAX) + black_box(1u8);
                }),
            ),
            (
                panic_const_sub_overflow,
                Box::new(|| {
                    let _ = black_box(0u8) - black_box(1u8);
                }),
            ),
            (
                panic_const_mul_overflow,
                Box::new(|| {
                    let _ = black_box(u8::MAX) * black_box(2u8);
                }),
            ),
            (
                panic_const_div_overflow,
                Box::new(|| {
                    let _ = black_box(i8::MIN) / black_box(-1i8);
                }),
            ),
            (
                panic_const_rem_overflow,
                Box::new(|| {
                    let _ = black_box(i8::MIN) % black_box(-1i8);
                }),
            ),
            (
                panic_const_neg_overflow,
                Box::new(|| {
                    let _ = -black_box(i8::MIN);
                }),
            ),
            (
                panic_const_shl_overflow,
                Box::new(|| {
                    let _ = black_box(1u8) << black_box(8u32);
                }),
            ),
            (
                panic_const_shr_overflow,
                Box::new(|| {
                    let _ = black_box(1u8) >> black_box(8u32);
                }),
            ),
            (
                panic_const_div_by_zero,
                Box::new(|| {
                    let _ = black_box(1u8) / black_box(0u8);
                }),
            ),
            (
                panic_const_rem_by_zero,
                Box::new(|| {
                    let _ = black_box(1u8) % black_box(0u8);
                }),
            ),
        ];

        for (model, real) in cases {
            assert_eq!(message_of(move || model()), message_of(real));
        }
    }

    #[test]
    fn test_panic_display() {
        panics_like_core(|| super::panic_display(&7u8), || panic!("{}", 7u8));
    }

    #[test]
    fn test_unreachable_display() {
        panics_like_core(
            || super::unreachable_display(&7u8),
            || unreachable!("{}", 7u8),
        );
    }

    // Reachable only from 2015-edition code; compared with what it forwards to.
    #[test]
    fn test_panic_str_2015() {
        panics_like_core(|| super::panic_str_2015("boom"), || panic!("{}", "boom"));
    }

    // Real core aborts or runs these at const-eval only, so only divergence is checked.
    #[test]
    #[should_panic]
    fn test_panic_nounwind() {
        super::panic_nounwind("boom");
    }

    #[test]
    #[should_panic]
    fn test_panic_nounwind_nobacktrace() {
        super::panic_nounwind_nobacktrace("boom");
    }

    #[test]
    #[should_panic]
    fn test_panic_nounwind_fmt() {
        super::panic_nounwind_fmt(crate::fmt::Arguments(&()), false);
    }

    #[test]
    #[should_panic]
    fn test_const_panic_fmt() {
        super::const_panic_fmt(crate::fmt::Arguments(&()));
    }

    #[test]
    #[should_panic]
    fn test_panic_explicit() {
        super::panic_explicit()
    }

    #[test]
    #[should_panic]
    fn test_panic() {
        super::panic("boom")
    }

    #[test]
    #[should_panic]
    fn test_internal_panic() {
        super::internal::panic::<()>()
    }
}
