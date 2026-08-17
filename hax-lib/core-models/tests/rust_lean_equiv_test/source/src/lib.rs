//! Rust↔Lean equivalence tests.
//!
//! Each `#[rust_lean_test] pub fn ... -> bool { ... }` in the submodules
//! below pins down a single observation about how a `core::*` / `std::*`
//! item behaves on a concrete input. The framework checks the same
//! observation twice:
//!
//! - **Rust side**: `cargo test` runs the function and asserts it returns
//!   `true`. (The `#[rust_lean_test]` attribute generates the
//!   `#[test]` wrapper.)
//! - **Lean side**: `gen_lean_tests.py` scans every file under `src/`
//!   for these attributes and emits a `#guard <qualified-name> == .ok true`
//!   per test into `lean/RustLeanTests/LeanTests.lean`, so the Lean build
//!   fails if Aeneas's translation of the function does not also evaluate
//!   to `RustM.ok true`.
//!
//! Agreement between the two sides is the actual property under test:
//! the Lean translation of our `core_models` library must match Rust
//! std's behaviour on every input we exercise here.
//!
//! ## Layout
//!
//! Mirrors the structure of the `core-models` crate so a contributor
//! adding a new item to `core-models/src/core/foo.rs` knows exactly
//! where to add the matching equivalence tests
//! (`source/src/core/foo.rs`).

// `core::hint::{likely, unlikely}` and `core::hint::cold_path` (exercised in
// `core::hint`) are still unstable.
#![feature(
    cmp_minmax,
    cold_path,
    drop_guard,
    ergonomic_clones,
    likely_unlikely,
    mem_copy_fn
)]
#![allow(incomplete_features)]
#![allow(unused_comparisons)]
// `div_floor`, `next_multiple_of` and `checked_next_multiple_of` are still
// unstable in std, so exercising them here needs the gate.
#![feature(int_roundings)]

pub mod helpers;

pub mod alloc;
pub mod core;
