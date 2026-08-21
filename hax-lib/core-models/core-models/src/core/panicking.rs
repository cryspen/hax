//! Model of `core::panicking`.
//!
//! Every function here diverges. Each one keeps `core`'s signature and is
//! `#[hax_lib::requires(false)]`, so no verified caller can reach it; the
//! `panic!()` bodies are what `cargo test` runs.
//!
//! The items are not doc-linked: `core::panicking` is `#[unstable]` and has no
//! `std` re-export, so there is no resolvable path to point rustdoc at.

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

/// `core::panicking::panic_nounwind`. The model does not distinguish unwinding
/// from aborting, so this is `panic` by another name.
//
// DEVIATION(std): std's parameter is `&'static str`; as with `panic` above the
// model takes a plain `&str`, because Aeneas cannot translate a body whose
// argument carries an explicit `'static`.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_nounwind(_expr: &str) -> ! {
    panic!()
}

/// `core::panicking::panic_nounwind_nobacktrace`. Backtraces are not modeled;
/// the `&str` deviation is the same as for `panic_nounwind`.
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

/// `core::panicking::const_panic_fmt` — what const-eval calls in place of
/// `panic_fmt`.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn const_panic_fmt(_fmt: super::fmt::Arguments) -> ! {
    panic!()
}

/// `core::panicking::panic_str_2015`, the 2015-edition `panic!(var)` entry point.
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

/// `core::panicking::panic_const` — the shims rustc lowers a MIR `Assert` to,
/// one per assertion kind, so that a failing check does not have to embed its
/// message at the call site. Nothing calls them from Rust source; they exist so
/// that the arithmetic-overflow, division-by-zero and
/// coroutine-resumed-after-completion panics have a name in the model.
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

    /// The arithmetic shims: rustc lowers the overflow / divide-by-zero MIR
    /// assertions to these, so the reachable `core` counterpart is the operation
    /// that trips the assertion. `black_box` keeps it out of const-eval, which
    /// would reject the program instead of panicking at run time.
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

    // The coroutine / `async fn` / `gen fn` shims have no `panics_like_core`
    // partner: reaching them means resuming a completed (or panicked, or
    // async-dropped) coroutine, and coroutines, `gen` blocks and async drop are
    // all unstable — there is no stable Rust that trips these assertions. So
    // these tests only pin that the model diverges.
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

    /// Each `panic_const_*` message must be the one rustc's assertion carries,
    /// so that a model panic is attributable to the same assertion as the real
    /// one. Compared against the message `core` actually produces.
    #[test]
    fn test_panic_const_messages_match_core() {
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

    /// `panic_display` and `unreachable_display` are what `panic!("{}", x)` and
    /// `unreachable!("{}", x)` reduce to, message included.
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

    /// `panic_str_2015` is only reachable from a 2015-edition `panic!(var)`; the
    /// closest reachable panic is the `panic_display` it forwards to.
    #[test]
    fn test_panic_str_2015() {
        panics_like_core(|| super::panic_str_2015("boom"), || panic!("{}", "boom"));
    }

    // `panic_nounwind*` abort in real `core` rather than unwind, so
    // `panics_like_core` cannot observe the `core` side at all (the process would
    // die); `const_panic_fmt` is a const-eval hook with no run-time caller. These
    // only pin that the model diverges.
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

    // The pre-existing diverging helpers. `should_panic` is the only way to run
    // them: `core::panicking` is internal, so there is no counterpart to pass to
    // `panics_like_core`.
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
