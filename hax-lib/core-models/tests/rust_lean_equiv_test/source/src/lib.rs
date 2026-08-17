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
    allocator_api,
    box_into_boxed_slice,
    box_into_inner,
    cmp_minmax,
    cold_path,
    cow_is_borrowed,
    disjoint_bitor,
    drop_guard,
    ergonomic_clones,
    formatting_options,
    funnel_shifts,
    int_format_into,
    int_lowest_highest_one,
    int_roundings,
    is_ascii_octdigit,
    isolate_most_least_significant_one,
    iter_advance_by,
    likely_unlikely,
    mem_copy_fn,
    push_mut,
    slice_split_once,
    slice_swap_unchecked,
    smart_pointer_try_map,
    strip_circumfix,
    trim_prefix_suffix,
    try_with_capacity,
    uint_bit_width,
    unchecked_shifts,
    utf16_extra,
    vec_try_remove,
    wrapping_int_impl,
    wrapping_next_power_of_two
)]
#![allow(incomplete_features)]
// Some tests deliberately exercise edge comparisons like `u8::MAX < 0u8`
// to pin trait-dispatch behaviour at the extremes; rustc warns those are
// tautologically false, but that *is* the observation under test.
#![allow(unused_comparisons)]
// `Cow::is_borrowed` / `Cow::is_owned` are still unstable in the real `alloc`.
#![feature(cow_is_borrowed)]

pub mod helpers;

pub mod alloc;
pub mod core;
