//! Equivalence tests for `core::panicking::*` — there are none, and cannot be.
//!
//! Two independent reasons:
//!
//! 1. **Nothing to observe.** Every item in `core::panicking` returns `!`. A
//!    `#[rust_lean_test]` is a `() -> bool` whose Rust half must return `true`
//!    and whose Lean half must evaluate to `Result.ok true`; a diverging call
//!    gives `Result.fail panic` on the Lean side and an aborted test on the Rust
//!    side, so there is no observation the framework can pin. (That is why no
//!    other module's equivalence tests exercise panicking paths either — the
//!    panic behaviour of e.g. `Option::unwrap` is checked in the model crate's
//!    own `#[cfg(test)]` block with `crate::testing::panics_like_core`.)
//!
//! 2. **No call path.** `core::panicking` is `#[unstable(feature =
//!    "panic_internals")]`, and the `panic_const_*` family are `#[lang]` items
//!    that rustc synthesises from MIR `Assert`s — no Rust source calls them by
//!    name. This crate is built on the stable surface, so it cannot name them at
//!    all.
//!
//! The model side is covered instead by `core-models/src/core/panicking.rs`'s
//! `#[cfg(test)]` block: each arithmetic `panic_const_*` shim is paired with the
//! operation that actually trips its assertion in real `core` (via
//! `panics_like_core`), and their panic messages are compared against the
//! messages `core` produces. The coroutine/`async fn`/`gen fn` shims, the
//! `panic_nounwind*` family and `const_panic_fmt` have no reachable `core`
//! counterpart on a stable toolchain and are only checked to diverge.
