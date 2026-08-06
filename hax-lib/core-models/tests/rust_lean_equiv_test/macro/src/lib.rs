//! `#[rust_lean_test]` — attribute macro for the rust↔lean equivalence
//! testing framework.
//!
//! Applied to a `pub fn foo() -> bool { ... }`, it leaves the function
//! untouched (so charon/Aeneas can extract it) and additionally emits a
//! `#[cfg(test)] #[test]` wrapper that asserts `foo()` returns `true` on
//! the Rust side. The Lean-side equivalent (`#guard foo == .ok true`) is
//! emitted into a generated `Tests/LeanTests.lean` file by the
//! `gen_lean_tests.py` script that scans the source for this attribute.
//!
//! # Skipping the Lean half
//!
//! `#[rust_lean_test(skip_lean = "why")]` keeps the Rust half running but emits
//! no `#guard`. `make check-skipped` fails if a skipped test starts passing.
//!
//! Only for extractions that elaborate and disagree. One that fails to
//! elaborate breaks the build with or without a guard — comment those out.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{ItemFn, LitStr, parse_macro_input};

#[proc_macro_attribute]
pub fn rust_lean_test(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut skip_lean: Option<LitStr> = None;
    if !attr.is_empty() {
        let parser = syn::meta::parser(|meta| {
            if meta.path.is_ident("skip_lean") {
                skip_lean = Some(meta.value()?.parse()?);
                Ok(())
            } else {
                Err(meta.error("expected `skip_lean = \"reason\"`"))
            }
        });
        parse_macro_input!(attr with parser);
    }
    // `check-skipped` reports the reason, so an empty one is a mistake.
    if let Some(reason) = &skip_lean {
        if reason.value().trim().is_empty() {
            return syn::Error::new_spanned(reason, "`skip_lean` needs a reason")
                .to_compile_error()
                .into();
        }
    }

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
