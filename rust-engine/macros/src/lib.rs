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
use syn::{Token, parse_macro_input, visit_mut::VisitMut};
use utils::*;

mod partial_application;
mod replace;
mod struct_fields;

/// Adds a new field with a fresh name to an existing `struct` type definition.
/// The new field contains error handling and span information to be used with a
/// visitor. This macro will also derive implementations of
/// [`hax_rust_engine::ast::visitors::wrappers::VisitorWithErrors`] and
/// [`hax_rust_engine::ast::HasSpan`] for the struct.
#[proc_macro_attribute]
pub fn setup_error_handling_struct(_attr: TokenStream, item: TokenStream) -> TokenStream {
    struct_fields::setup_error_handling_struct(_attr, item)
}

/// Adds a new field with a fresh name to an existing `struct` type definition.
/// The new field contains error handling and span information to be used with a
/// visitor. This macro will also derive implementations of
/// [`hax_rust_engine::ast::visitors::wrappers::VisitorWithErrors`] and
/// [`hax_rust_engine::ast::HasSpan`] for the struct.
#[proc_macro_attribute]
pub fn setup_span_handling_struct(_attr: TokenStream, item: TokenStream) -> TokenStream {
    struct_fields::setup_span_handling_struct(_attr, item)
}

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

    pub(crate) fn krate() -> proc_macro2::TokenStream {
        use proc_macro_crate::{FoundCrate, crate_name};
        match crate_name("hax-rust-engine").unwrap() {
            FoundCrate::Itself => quote!(crate),
            FoundCrate::Name(name) => {
                let ident = Ident::new(&name, Span::call_site());
                quote!( #ident )
            }
        }
    }
}

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
        quote! {Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, derive_generic_visitor::Drive, derive_generic_visitor::DriveMut},
    )
}

#[proc_macro_attribute]
/// Replaces all occurrences of an identifier within the attached item.
///
/// For example, `#[replace(Name => A, B, C)]` will replace `Name` by `A, B, C`
/// in the item the proc-macro is applied on.
///
/// The special case `#[replace(Name => include(VisitableAstNodes))]` will
/// expand to a list of visitable AST nodes. This is useful in practice, as this
/// list is often repeated.
pub fn replace(attr: TokenStream, item: TokenStream) -> TokenStream {
    replace::replace(attr, item)
}

/// An attribute procedural macro that creates a new `macro_rules!` definition
/// by partially applying an existing macro or function with a given token stream.
///
/// Usage:
/// ```rust,ignore
/// #[partial_apply(original_macro!, my_expression,)]
/// macro_rules! new_proxy_macro {
///     // This content is ignored and replaced by the proc macro.
/// }
/// ```
#[proc_macro_attribute]
pub fn partial_apply(attr: TokenStream, item: TokenStream) -> TokenStream {
    partial_application::partial_apply(attr, item)
}

/// Prepend the body any associated function with the given attribute payload.
/// ```rust,ignore
/// #[prepend_associated_functions_with(println!("self is {self}");)]
/// impl Foo {
///   fn f(self) {}
/// }
/// ```
///
/// Expands to:
/// ```rust,ignore
/// impl Foo {
///   fn f(self) {
///     println!("self is {self}");
///   }
/// }
/// ```
#[proc_macro_attribute]
pub fn prepend_associated_functions_with(attr: TokenStream, item: TokenStream) -> TokenStream {
    struct Visitor {
        prefix: syn::Expr,
    }
    impl VisitMut for Visitor {
        fn visit_item_impl_mut(&mut self, impl_block: &mut syn::ItemImpl) {
            for item in &mut impl_block.items {
                let syn::ImplItem::Fn(impl_item_fn) = item else {
                    continue;
                };
                impl_item_fn.block.stmts.insert(
                    0,
                    syn::Stmt::Expr(self.prefix.clone(), Some(Token![;](Span::mixed_site()))),
                );
            }
        }
    }
    let mut item: syn::Item = parse_macro_input!(item);
    let prefix = parse_macro_input!(attr);
    Visitor { prefix }.visit_item_mut(&mut item);
    quote! {#item}.into()
}
