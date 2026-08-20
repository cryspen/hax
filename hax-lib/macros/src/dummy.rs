//! Fallbacks used when hax is not running: the proc-macros of this crate should
//! then be transparent. Only the macros that cannot simply forward their input
//! need an implementation here.

use crate::hax_paths::*;
use proc_macro::{TokenStream, TokenTree};
use quote::quote;
use syn::{visit_mut::VisitMut, *};

/// Expansion of a `<BACKEND>_expr!` macro.
pub fn unit_expr() -> TokenStream {
    quote! { () }.into()
}

/// Expansion of a `<BACKEND>_prop_expr!` macro.
pub fn prop_expr() -> TokenStream {
    quote! {::hax_lib::Prop::from_bool(true)}.into()
}

/// Expansion of a `<BACKEND>_unsafe_expr!` macro. Such a macro generates a Rust
/// expression of any type, that gets replaced by verbatim backend code at
/// extraction: it is meaningful only in hax-only contexts, so reaching this
/// point means the user broke that rule.
pub fn unsafe_expr() -> TokenStream {
    quote! { ::std::compile_error!("`hax_lib::unsafe_expr` has no meaning outside of hax extraction, please use it solely on hax-only places.") }.into()
}

/// Expansion of an internal macro that was used directly.
pub fn internal_macro_misuse(name: &str) -> TokenStream {
    let message = format!("`{name}` is an internal macro and should never be used directly.");
    quote! { ::std::compile_error!(#message) }.into()
}

fn not_hax_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !matches!(expects_path_decoration(&ml.path), Ok(Some(_)))
    } else {
        true
    }
}

fn not_field_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !(matches!(expects_refine(&ml.path), Ok(Some(_)))
            || matches!(expects_order(&ml.path), Ok(Some(_))))
    } else {
        true
    }
}

/// Strips the hax attributes enabled by `#[attributes]`.
pub fn attributes(item: TokenStream) -> TokenStream {
    let item: Item = parse_macro_input!(item);

    struct AttrVisitor;

    use syn::visit_mut;
    impl VisitMut for AttrVisitor {
        fn visit_item_trait_mut(&mut self, item: &mut ItemTrait) {
            for ti in item.items.iter_mut() {
                if let TraitItem::Fn(fun) = ti {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_trait_mut(self, item);
        }
        fn visit_type_mut(&mut self, _type: &mut Type) {}
        fn visit_item_impl_mut(&mut self, item: &mut ItemImpl) {
            for ii in item.items.iter_mut() {
                if let ImplItem::Fn(fun) = ii {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_impl_mut(self, item);
        }
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);

            match item {
                Item::Struct(s) => {
                    for field in s.fields.iter_mut() {
                        field.attrs.retain(not_field_attribute)
                    }
                }
                _ => (),
            }
        }
    }

    let mut item = item;
    AttrVisitor.visit_item_mut(&mut item);

    quote! { #item }.into()
}

/// Expansion of `int!`.
pub fn int(payload: TokenStream) -> TokenStream {
    let mut tokens = payload.into_iter().peekable();
    let negative = matches!(tokens.peek(), Some(TokenTree::Punct(p)) if p.as_char() == '-');
    if negative {
        tokens.next();
    }
    let [lit @ TokenTree::Literal(_)] = &tokens.collect::<Vec<_>>()[..] else {
        return quote! { ::std::compile_error!("Expected exactly one numeric literal") }.into();
    };
    let lit: proc_macro2::TokenStream = TokenStream::from(lit.clone()).into();
    quote! {::hax_lib::int::Int(#lit)}.into()
}
