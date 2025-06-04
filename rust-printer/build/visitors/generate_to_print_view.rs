use super::ast_with_contextes::WrapTypesWithCtx;
use super::utils;

use quote::quote;
use syn::{parse_quote, visit_mut::VisitMut, Fields, Item};

pub struct GenerateBridges;

fn make_branch(constructor: proc_macro2::TokenStream, fields: &Fields) -> proc_macro2::TokenStream {
    let fields_idents = utils::field_idents(fields.iter());
    let payload = utils::fields_to_payload(fields);
    quote! {
        origin::#constructor #payload => {
            #(
                let #fields_idents = {
                    let context = PrintContext {
                        value: #fields_idents,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(#constructor), "::", stringify!(#fields_idents)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
            )*
            destination::#constructor #payload
        }
    }
}

impl VisitMut for GenerateBridges {
    fn visit_item_mut(&mut self, item: &mut syn::Item) {
        let branches = match item {
            Item::Struct(i) => {
                let type_ident = &i.ident;
                let branches = vec![make_branch(quote! {#type_ident}, &i.fields)];
                Some(branches)
            }
            Item::Enum(i) => {
                let type_ident = &i.ident;
                let branches: Vec<_> = i
                    .variants
                    .iter()
                    .map(|variant| {
                        let ident = &variant.ident;
                        make_branch(quote! {#type_ident::#ident}, &variant.fields)
                    })
                    .collect();
                Some(branches)
            }
            _ => None,
        };
        let Some(branches) = branches else { return };

        let branches = if branches.is_empty() {
            vec![
                quote! {_ => unreachable!("no variant, but references are always inhabited (see https://github.com/rust-lang/rust/issues/78123)")},
            ]
        } else {
            branches
        };

        let item_destination = {
            let mut item = item.clone();
            WrapTypesWithCtx.visit_item_mut(&mut item);
            utils::RemoveUnusedLifetimes.visit_item_mut(&mut item);
            item
        };
        let type_ident = utils::ident_of_item(item);
        let generics_destination = utils::generics_of_item(&item_destination);
        *item = parse_quote! {
            impl<'a> ToPrintView<'a> for origin::#type_ident {
                type Out = destination::#type_ident #generics_destination;
                fn to_print_view(&'a self, #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>) -> Self::Out {
                    match self {
                        #(#branches),*
                    }
                }
            }
        }
    }
}
