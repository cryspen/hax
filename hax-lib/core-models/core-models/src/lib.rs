//! `core-models`: A Rust Model for the `core` Library
//!
//! `core-models` is a simplified, self-contained model of Rust’s `core` library. It aims to provide
//! a purely Rust-based specification of `core`'s fundamental operations, making them easier to
//! understand, analyze, and formally verify. Unlike `core`, which may rely on platform-specific
//! intrinsics and compiler magic, `core-models` expresses everything in plain Rust, prioritizing
//! clarity and explicitness over efficiency.
//!
//! ## Key Features
//!
//! - **Partial Modeling**: `core-models` includes only a subset of `core`, focusing on modeling
//!   fundamental operations rather than providing a complete replacement.
//! - **Exact Signatures**: Any item that exists in both `core-models` and `core` has the same type signature,
//!   ensuring compatibility with formal verification efforts.
//! - **Purely Functional Approach**: Where possible, `core-models` favors functional programming principles,
//!   avoiding unnecessary mutation and side effects to facilitate formal reasoning.
//! - **Explicit Implementations**: Even low-level operations, such as SIMD, are modeled explicitly using
//!   Rust constructs like bit arrays and partial maps.
//! - **Extra Abstractions**: `core-models` includes additional helper types and functions to support
//!   modeling. These extra items are marked appropriately to distinguish them from `core` definitions.
//!
//! ## Intended Use
//!
//! `core-models` is designed as a reference model for formal verification and reasoning about Rust programs.
//! By providing a readable, well-specified version of `core`'s behavior, it serves as a foundation for
//! proof assistants and other verification tools.

#![allow(dead_code, unused)]
// `coverage(off)` is unstable; `cfg(coverage_nightly)` is set only by
// `cargo llvm-cov`, so normal builds and extraction never see this.
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]
// int_roundings: lets the proptests call std's still-unstable signed `div_ceil`.

// likely_unlikely/cold_path: same, for the `hint` proptests.
#![cfg_attr(
    test,
    feature(
        array_into_iter_constructors,
        bound_as_ref,
        bound_copied,
        cmp_minmax,
        cold_path,
        control_flow_into_value,
        control_flow_ok,
        disjoint_bitor,
        drop_guard,
        exact_div,
        funnel_shifts,
        hasher_prefixfree_extras,
        int_lowest_highest_one,
        int_roundings,
        is_ascii_octdigit,
        isolate_most_least_significant_one,
        likely_unlikely,
        mem_copy_fn,
        nonzero_bitwise,
        nonzero_ops,
        one_sided_range,
        range_bounds_is_empty,
        range_into_bounds,
        step_trait,
        uint_bit_width,
        unchecked_neg,
        unchecked_shifts,
        utf16_extra,
        wrapping_int_impl,
        wrapping_next_power_of_two
    )
)]
// likely_unlikely/cold_path: same, for the `hint` proptests.

// hasher_prefixfree_extras: same, for `Hasher::{write_length_prefix, write_str}`.

// cmp_minmax: same, for `cmp::minmax{,_by,_by_key}`.

// array_into_iter_constructors: `core::array::IntoIter::empty` is still
// unstable, and a proptest compares against it.

// mem_copy_fn / drop_guard: same, for `core::mem::{copy, DropGuard}`.
// The `bound_*` / `control_flow_*` / `range_*` / `one_sided_range` features let
// the `ops` proptests call the still-unstable std counterparts of the range and
// `ControlFlow` items the model provides.
// The proptests compare the model against std counterparts that are still
// unstable: `div_ceil`/`div_floor`/`next_multiple_of` (int_roundings),
// `exact_div` (exact_div, which is what the pinned toolchain calls the method
// rustdoc now names `div_exact`), and `unchecked_neg`.

#[path = "core/array.rs"]
pub mod array;
#[path = "core/borrow.rs"]
pub mod borrow;
#[path = "core/clone.rs"]
pub mod clone;
#[path = "core/cmp.rs"]
pub mod cmp;
#[path = "core/convert.rs"]
pub mod convert;
#[path = "core/default.rs"]
pub mod default;
#[path = "core/error.rs"]
pub mod error;
#[path = "core/f32.rs"]
pub mod f32;
#[path = "core/fmt.rs"]
pub mod fmt;
#[path = "core/hash.rs"]
pub mod hash;
#[path = "core/hint.rs"]
pub mod hint;
#[path = "core/intrinsics.rs"]
pub mod intrinsics;
#[path = "core/iter.rs"]
pub mod iter;
#[path = "core/marker.rs"]
pub mod marker;
#[path = "core/mem.rs"]
pub mod mem;
#[path = "core/num/mod.rs"]
pub mod num;
#[path = "core/ops.rs"]
pub mod ops;
#[path = "core/option.rs"]
pub mod option;
#[path = "core/panicking.rs"]
pub mod panicking;
#[path = "core/result.rs"]
pub mod result;
#[path = "core/slice.rs"]
pub mod slice;
#[path = "core/str.rs"]
pub mod str;

#[cfg(test)]
pub mod testing;
