//! Shared utilities used across the equivalence-test modules.
//!
//! ## Why `none_T()` helpers
//!
//! Aeneas's pretty printer erases the type parameter of bare `None`
//! values that aren't anchored by a call site, so the extracted Lean
//! emits a polymorphic `Option.None` whose `T` Lean cannot infer.
//! Routing through a typed helper that constructs `None` via
//! `Some(default).take()` keeps the local typed in MIR and survives
//! extraction. Use these helpers anywhere you need a typed `None` in
//! a zero-arg test.
//!
//! Add a new `none_<T>` when you exercise an `Option<T>` for which one
//! doesn't already exist.

macro_rules! none_helper {
    ($name:ident, $t:ty, $default:expr) => {
        pub fn $name() -> Option<$t> {
            let mut x: Option<$t> = Some($default);
            x.take();
            x
        }
    };
}

none_helper!(none_u8, u8, 0);
none_helper!(none_u16, u16, 0);
none_helper!(none_u32, u32, 0);
none_helper!(none_u64, u64, 0);
none_helper!(none_usize, usize, 0);
none_helper!(none_i8, i8, 0);
none_helper!(none_i16, i16, 0);
none_helper!(none_i32, i32, 0);
none_helper!(none_i64, i64, 0);
none_helper!(none_isize, isize, 0);
none_helper!(none_bool, bool, false);
