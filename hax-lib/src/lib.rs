#![doc = include_str!("../README.md")]
#![no_std]

#[cfg(feature = "macros")]
mod proc_macros;

// hax engine relies on `hax-lib` names: to avoid cluttering names with
// an additional `implementation` in all paths, we `include!` instead
// of doing conditional `mod` and `pub use`.

#[cfg(not(hax))]
core::include!("dummy.rs");
#[cfg(hax)]
core::include!("implementation.rs");
