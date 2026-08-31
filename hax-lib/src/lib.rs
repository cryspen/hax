//! Hax-specific helpers for Rust programs. Those helpers are usually
//! no-ops when compiled normally but meaningful when compiled under
//! hax.
//!
//! # Example:
//!
//! ```rust
//! #[hax_lib::requires(hax_lib::Prop::from(x.len() == y.len()) & hax_lib::forall(
//!     |i: usize| hax_lib::implies(
//!         i < x.len(),
//!         x[i] as u64 + y[i] as u64 <= u32::MAX as u64
//!     )
//! ))]
//! #[hax_lib::ensures(|result| result.len() == x.len())]
//! fn sum(x: Vec<u32>, y: Vec<u32>) -> Vec<u32> {
//!     x.into_iter().zip(y).map(|(x, y)| x + y).collect()
//! }
//! ```

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
