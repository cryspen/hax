//! Helper crate providing procedural macros for the Rust engine of hax.
//!
//! Currently it provides the following.
//!  - Macros for deriving groups of traits.
//!    Most of the type from the AST have the same bounds, so that helps deduplicating a lot.
//!    Also, the fact those derive groups are named is helpful: for instance for code generation
//!    a simple `use derive_group_for_ast_base as derive_group_for_ast` can change what is to be
//!    derived without any attribute manipulation.

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;

mod utils {
    use super::*;
    pub(crate) fn crate_name() -> Ident {
        let krate = module_path!().split("::").next().unwrap();
        Ident::new(krate, Span::call_site())
    }

    /// Prepends a `proc_macro2::TokenStream` to a `TokenStream`
    pub(crate) fn prepend(item: TokenStream, prefix: proc_macro2::TokenStream) -> TokenStream {
        let item: proc_macro2::TokenStream = item.into();
        quote! {
            #prefix
            #item
        }
        .into()
    }

    /// Add a derive attribute to `item`
    pub(crate) fn add_derive(item: TokenStream, payload: proc_macro2::TokenStream) -> TokenStream {
        prepend(item, quote! {#[derive(#payload)]})
    }
}
use utils::*;

/// Derive the common derives for the hax engine AST.
/// This is a equivalent to `derive_group_for_ast_serialization` and `derive_group_for_ast_base`.
#[proc_macro_attribute]
pub fn derive_group_for_ast(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let krate = crate_name();
    prepend(
        item,
        quote! {
            #[#krate::derive_group_for_ast_base]
            #[#krate::derive_group_for_ast_serialization]
        },
    )
}

/// Derive the necessary [de]serialization related traits for nodes in the AST.
#[proc_macro_attribute]
pub fn derive_group_for_ast_serialization(_attr: TokenStream, item: TokenStream) -> TokenStream {
    add_derive(
        item,
        quote! {::serde::Deserialize, ::serde::Serialize, ::schemars::JsonSchema},
    )
}

/// Derive the basic necessary traits for nodes in the AST.
#[proc_macro_attribute]
pub fn derive_group_for_ast_base(_attr: TokenStream, item: TokenStream) -> TokenStream {
    add_derive(
        item,
        quote! {Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord},
    )
}
