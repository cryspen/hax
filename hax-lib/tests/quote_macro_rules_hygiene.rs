//! Regression test: quotation macros (`fstar!` & friends) must work when
//! invoked *through a `macro_rules!` wrapper*.
//!
//! Antiquotation snippets are parsed out of the payload string's contents,
//! so the macro has to pick a span for the tokens it synthesizes. Using
//! `Span::call_site()` breaks the wrapper case: the call site is then the
//! wrapper's expansion context and `$local` antiquotations fail to resolve
//! (E0425). The macro now re-spans antiquotation tokens onto the payload
//! string literal itself, which travels through wrappers carrying the
//! user's span.
//!
//! This is a plain compile test: under `--cfg hax`, `fstar!` expands to
//! real bindings for every antiquotation, so name resolution is checked by
//! building this file with `RUSTFLAGS='--cfg hax'` (the `hax-lib` CI job
//! does this; without the cfg the macros expand to nothing and the test is
//! trivially green, which is fine — it then just checks the non-hax path).

/// A user-side wrapper, as a project might define to demarcate proof
/// annotations from code.
macro_rules! proof {
    ($s:literal) => {
        ::hax_lib::fstar!($s)
    };
}

/// Wrapper with its own indirection level (two nested `macro_rules!`).
macro_rules! proof2 {
    ($s:literal) => {
        proof!($s)
    };
}

#[allow(dead_code)]
fn antiquote_through_wrapper(x: u32) -> u32 {
    let y = x.wrapping_add(1);
    proof!("some f* code mentioning $x and ${y}");
    proof2!("more f* code: ${x} $y");
    // Direct invocation (the historical path) must keep working identically.
    hax_lib::fstar!("direct: $x ${y}");
    y
}

#[test]
fn compiles() {
    // The value of this test is that the file *type-checks* under
    // `--cfg hax`; there is nothing to run.
    assert_eq!(antiquote_through_wrapper(1), 2);
}
