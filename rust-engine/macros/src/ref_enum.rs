use std::collections::HashSet;

use convert_case::{Case, Casing};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    token::Comma,
    visit_mut::{self, VisitMut},
    Data, DeriveInput, Fields, GenericArgument, GenericParam, Ident, LifetimeDef, PathArguments,
    Type, TypePath,
};

/// A visitor that rewrites any simple `Foo` or `Foo<…>` into `super::Foo`
/// if `"Foo"` is in `to_rewrite`.
pub struct SimpleIdentRewriter<'a>(&'a HashSet<&'a Ident>);

impl<'a> VisitMut for SimpleIdentRewriter<'a> {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        // First, recurse into any sub-types:
        visit_mut::visit_type_mut(self, ty);

        // Now check whether this is a plain path with exactly one segment:
        if let Type::Path(type_path) = ty {
            let path = &type_path.path;
            if type_path.qself.is_none() && path.leading_colon.is_none() && path.segments.len() == 1
            {
                let segment = &path.segments[0];
                match &segment.arguments {
                    PathArguments::None | PathArguments::AngleBracketed(_)
                        if self.0.contains(&segment.ident) =>
                    {
                        *ty = parse_quote! { super::#ty }
                    }
                    _ => {}
                }
            }
        }
    }
}

pub struct VecToSlice;

impl VisitMut for VecToSlice {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        // Recurse first (so inner Vecs get rewritten before outer types)
        visit_mut::visit_type_mut(self, ty);

        // Now try to match `Type::Path` == `Vec<...>`
        if let Type::Path(TypePath { path, .. }) = ty {
            // single-segment path named "Vec"
            if path.segments.len() == 1 && path.segments[0].ident == "Vec" {
                if let PathArguments::AngleBracketed(ref args) = path.segments[0].arguments {
                    // exactly one type argument
                    if args.args.len() == 1 {
                        if let GenericArgument::Type(elem_ty) = &args.args[0] {
                            // Construct `&'a [Elem]`
                            let new_ty: Type = parse_quote! {
                                [#elem_ty]
                            };
                            *ty = new_ty;
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn derive_ref_enum(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let Data::Enum(data) = &input.data else {
        panic!("Not an enum")
    };
    let variant_names: HashSet<&Ident> = HashSet::from_iter(data.variants.iter().map(|v| &v.ident));

    let enum_name = input.ident;
    let enum_name_sc = Ident::new(
        &enum_name.to_string().to_case(Case::Snake),
        Span::call_site(),
    );

    let trait_name = Ident::new(&format!("Destruct{}", enum_name), Span::call_site());

    let variants = data
        .variants
        .iter()
        .map(|v| {
            (
                &v.ident,
                match &v.fields {
                    Fields::Named(fields_named) => fields_named.named.iter().collect(),
                    Fields::Unnamed(fields_unnamed) => fields_unnamed.unnamed.iter().collect(),
                    Fields::Unit => vec![],
                },
                match &v.fields {
                    Fields::Named { .. } => |ts| quote! { { #ts } },
                    Fields::Unnamed { .. } => |ts| quote! { ( #ts ) },
                    Fields::Unit => |ts| ts,
                },
                if matches!(&v.fields, Fields::Named { .. }) {
                    quote!()
                } else {
                    quote!(;)
                },
            )
        })
        .collect::<Vec<_>>();

    let trait_methods: Vec<_> = variants
        .iter()
        .map(|(v_name, fields, _, _)| {
            let method_name = Ident::new(
                &format!("expect_{}", v_name),
                proc_macro2::Span::call_site(),
            );
            let generics = (!fields.is_empty()).then_some(quote! {<RefKind>});
            quote! {fn #method_name(self) -> Option<#enum_name_sc::#v_name #generics >;}
        })
        .collect();

    let mk_impl = |lifetime: proc_macro2::TokenStream,
                   mutable: proc_macro2::TokenStream,
                   ref_kind: proc_macro2::TokenStream| {
        let impl_methods = variants.iter().map(|(v_name, fields, wrap, _)| {
            let method_name = Ident::new(
                &format!("expect_{}", v_name),
                proc_macro2::Span::call_site(),
            );
            let generics = (!fields.is_empty()).then_some(ref_kind.clone());

            let payload = {
                let fields = fields.iter().enumerate().map(|(n, f)| {
                    f.ident
                        .clone()
                        .unwrap_or(Ident::new(&format!("field_{n}"), Span::call_site()))
                });
                wrap(quote!(#(#fields),*))
            };
            let out = {
                let fields = fields.iter().enumerate().map(|(n, f)| {
                    let default = Ident::new(&format!("field_{n}"), Span::call_site());
                    f.ident
                        .clone()
                        .map(|i| quote! {#i: &#mutable*#i})
                        .unwrap_or(quote!(&#mutable*#default))
                });
                wrap(quote!(#(#fields),*))
            };

            quote! {fn #method_name(self) -> Option<#enum_name_sc::#v_name<#generics>> {
                match self {
                    #enum_name::#v_name #payload => Some(#enum_name_sc :: #v_name :: <#generics> #out),
                    _ => None,
                }
            }}
        });
        quote! {
            impl<#lifetime> #trait_name<#ref_kind> for /*super::*/<#ref_kind as ref_kind::RefKind>::Ref<#enum_name> {
                #(#impl_methods)*
            }
        }
    };

    let structs = variants.iter().map(|(name, fields, wrap, semicolon)| {
        let generics = (!fields.is_empty()).then_some(quote! {<RefKind: ref_kind::RefKind>});
        let fields = fields.iter().map(|f| {
            let ident = f.ident.as_ref().map(|i| quote! {#i:});
            let mut ty = f.ty.clone();
            SimpleIdentRewriter(&variant_names).visit_type_mut(&mut ty);
            VecToSlice.visit_type_mut(&mut ty);
            quote!(pub #ident <RefKind as ref_kind::RefKind>::Ref<#ty>)
        });
        let payload = wrap(quote!(#(#fields),*));
        quote! {pub struct #name #generics #payload #semicolon}
    });

    let impls = [
        mk_impl(quote!('a), quote!(), quote!(ref_kind::Borrow<'a>)),
        mk_impl(quote!('a), quote!(mut), quote!(ref_kind::MutBorrow<'a>)),
        // mk_impl(quote!(), quote!(ref_kind::Own)),
    ];

    let expanded = quote! {
        pub mod #enum_name_sc {
            use super::*;
            #(#structs)*
        }
        pub trait #trait_name<RefKind: ref_kind::RefKind> {
            #(#trait_methods)*
        }
        #(#impls)*
    };

    std::fs::write(
        "/tmp/foo.rs",
        format!("{}", expanded.clone().into_token_stream()),
    );

    expanded.into()
}
