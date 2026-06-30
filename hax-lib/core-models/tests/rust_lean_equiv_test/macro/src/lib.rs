//! `#[rust_lean_test]` — attribute macro for the rust↔lean equivalence
//! testing framework.
//!
//! Applied to a `pub fn foo() -> bool { ... }`, it leaves the function
//! untouched (so charon/Aeneas can extract it) and additionally emits a
//! `#[cfg(test)] #[test]` wrapper that asserts `foo()` returns `true` on
//! the Rust side. The Lean-side equivalent (`#guard foo == .ok true`) is
//! emitted into a generated `Tests/LeanTests.lean` file by the
//! `gen_lean_tests.py` script that scans the source for this attribute.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{ItemFn, parse_macro_input};

#[proc_macro_attribute]
pub fn rust_lean_test(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = &input.sig.ident;
    let check_name = format_ident!("__rust_lean_test_{}", name);

    let expanded = quote! {
        #input

        #[cfg(test)]
        #[test]
        #[allow(non_snake_case)]
        fn #check_name() {
            assert!(
                #name(),
                concat!("rust_lean_test `", stringify!(#name), "` returned false"),
            );
        }
    };

    expanded.into()
}
