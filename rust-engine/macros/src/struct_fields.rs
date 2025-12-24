use crate::utils::*;
use proc_macro::TokenStream;
use proc_macro2::{Group, Ident, Span};
use quote::{ToTokens, quote};
use syn::{
    Field, FieldsUnnamed, Token, parse_macro_input, parse_quote, punctuated::Punctuated,
    token::Paren,
};

/// Adds a new field `extra_field_name` of type `extra_field_type` to an existing `struct` type definition.
/// `extra_field_name` is just a name hint, if a field with this name exists already, a different name will be picked.
/// Returns the actual name or `_N` (in the case of a tuple struct).
fn add_field_to_item_struct(
    item: &mut syn::ItemStruct,
    extra_field_name: &str,
    extra_field_type: syn::Type,
) -> proc_macro2::TokenStream {
    // Deal with the case of unit structs.
    if let fields @ syn::Fields::Unit = &mut item.fields {
        let span = Group::new(proc_macro2::Delimiter::Brace, fields.to_token_stream()).delim_span();
        *fields = syn::Fields::Unnamed(FieldsUnnamed {
            paren_token: Paren { span },
            unnamed: Punctuated::default(),
        })
    }
    /// Computes a fresh identifier given a list of existing identifiers.
    fn fresh_ident(base: &str, existing: &[Ident]) -> Ident {
        let existing: std::collections::HashSet<_> =
            existing.iter().map(|id| id.to_string()).collect();

        (0..)
            .map(|i| {
                if i == 0 {
                    base.to_string()
                } else {
                    format!("{}{}", base, i)
                }
            })
            .find(|name| !existing.contains(name))
            .map(|name| Ident::new(&name, Span::call_site()))
            .expect("should always find a fresh identifier")
    }
    // Collect fields, disregarding their kind (are they named or not)
    let (fields, named) = match &mut item.fields {
        syn::Fields::Named(fields_named) => (&mut fields_named.named, true),
        syn::Fields::Unnamed(fields_unnamed) => (&mut fields_unnamed.unnamed, false),
        syn::Fields::Unit => unreachable!("Unit structs were dealt with."),
    };

    let existing_names = fields
        .iter()
        .flat_map(|f| &f.ident)
        .cloned()
        .collect::<Vec<_>>();

    let (extra_field_ident, extra_field_ident_ts) = if named {
        let ident = fresh_ident(extra_field_name, &existing_names);
        (Some(ident.clone()), ident.to_token_stream())
    } else {
        (
            None,
            syn::LitInt::new(&format!("{}", fields.len()), Span::call_site()).to_token_stream(),
        )
    };

    fields.push(Field {
        attrs: vec![],
        vis: syn::Visibility::Inherited,
        mutability: syn::FieldMutability::None,
        ident: extra_field_ident,
        colon_token: named.then_some(Token![:](Span::call_site())),
        ty: extra_field_type,
    });

    extra_field_ident_ts
}

/// This function is documented in [`crate::setup_error_handling_struct`].
pub(crate) fn setup_error_handling_struct(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item: syn::ItemStruct = parse_macro_input!(item);
    let krate = rust_engine_krate_name();
    let extra_field_ident_ts = add_field_to_item_struct(
        &mut item,
        "error_handling_state",
        parse_quote! {#krate::ast::visitors::wrappers::ErrorHandlingState},
    );

    let struct_name = &item.ident;
    let generics = &item.generics;
    quote! {
        #item
        impl #generics #krate::ast::HasSpan for #struct_name #generics {
            fn span(&self) -> #krate::ast::span::Span {
                self.#extra_field_ident_ts.0.clone()
            }
            fn span_mut(&mut self) -> &mut #krate::ast::span::Span {
                &mut self.#extra_field_ident_ts.0
            }
        }
        impl #generics #krate::ast::visitors::wrappers::VisitorWithErrors for #struct_name #generics {
            fn error_vault(&mut self) -> &mut #krate::ast::visitors::wrappers::ErrorVault {
                &mut self.#extra_field_ident_ts.1
            }
        }
    }
    .into()
}

/// This function is documented in [`crate::setup_printer_struct`].
pub(crate) fn setup_printer_struct(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item: syn::ItemStruct = parse_macro_input!(item);
    let krate = rust_engine_krate_name();
    let extra_contextual_span_field_ident_ts = add_field_to_item_struct(
        &mut item,
        "contextual_span",
        parse_quote! {Option<#krate::ast::span::Span>},
    );
    let extra_linked_item_graph_field_ident_ts = add_field_to_item_struct(
        &mut item,
        "linked_item_graph",
        parse_quote! {::std::rc::Rc<#krate::attributes::LinkedItemGraph>},
    );

    let struct_name = &item.ident;
    let generics = &item.generics;
    quote! {
        #item
        impl #generics #krate::printer::pretty_ast::HasContextualSpan for #struct_name #generics {
            fn span(&self) -> Option<#krate::ast::span::Span> {
                self.#extra_contextual_span_field_ident_ts.clone()
            }
            fn with_span(&self, span: #krate::ast::span::Span) -> Self {
                let mut printer = self.clone();
                printer.#extra_contextual_span_field_ident_ts = Some(span);
                printer
            }
        }
        impl #generics #krate::printer::HasLinkedItemGraph for #struct_name #generics {
            fn linked_item_graph(&self) -> &#krate::attributes::LinkedItemGraph {
                &self.#extra_linked_item_graph_field_ident_ts
            }
            fn with_linked_item_graph(mut self, graph: ::std::rc::Rc<#krate::attributes::LinkedItemGraph>) -> Self {
                self.#extra_linked_item_graph_field_ident_ts = graph;
                self
            }
        }
    }
    .into()
}
