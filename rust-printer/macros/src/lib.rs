use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    visit::Visit,
    visit_mut::{self, VisitMut},
    Data, DataEnum, DeriveInput, GenericArgument, Ident, Path, PathArguments, Type, TypePath,
};

#[derive(Default)]
struct WrapperVisitor {
    pub types: Vec<Type>,
}

struct TypeReplacer {
    pub from: Ident,
    pub to: syn::QSelf,
}

impl VisitMut for TypeReplacer {
    fn visit_type_mut(&mut self, node: &mut Type) {
        if let Type::Path(TypePath {
            qself: qself @ None,
            path,
        }) = node
        {
            let mut it = path.segments.iter();
            if let Some(first) = it.next() {
                if first.ident == self.from {
                    path.segments = Punctuated::from_iter(it.cloned());
                    *qself = Some(self.to.clone());
                }
            }
        }
        visit_mut::visit_type_mut(self, node);
    }
}

impl<'ast> Visit<'ast> for WrapperVisitor {
    fn visit_type_path(&mut self, type_path: &'ast TypePath) {
        let segments: Vec<_> = type_path.path.segments.iter().collect();
        if let [t, wrapper] = &segments[..] {
            if t.ident == "T" && wrapper.ident == "Wrapper" {
                if let PathArguments::AngleBracketed(angle_args) = &wrapper.arguments {
                    if angle_args.args.len() == 1 {
                        if let GenericArgument::Type(ty) = angle_args.args.first().unwrap() {
                            self.types.push(ty.clone());
                        }
                    }
                }
            }
        }
        syn::visit::visit_type_path(self, type_path);
    }
}

#[proc_macro_attribute]
pub fn ast_derives(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let mut input = parse_macro_input!(input as DeriveInput);
    input
        .attrs
        .push(parse_quote! { #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, macros::Retyper)] });
    input.to_token_stream().into()
}

#[proc_macro_derive(Retyper)]
pub fn derive_retyper(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let item_ident = &input.ident;
    let body = match &input.data {
        Data::Union(..) => panic!("Union not supported"),
        Data::Enum(DataEnum { variants, .. }) => {
            let branches: Vec<_> = variants
                .iter()
                .map(|variant| {
                    let ident = &variant.ident;

                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            field.ident.clone().unwrap_or(Ident::new(
                                &format!("x{i}"),
                                proc_macro2::Span::call_site(),
                            ))
                        })
                        .collect();
                    let payload = {
                        match variant.fields {
                            syn::Fields::Named(..) => quote! { { #(#fields),* } },
                            syn::Fields::Unnamed(..) => quote! { ( #(#fields),* ) },
                            syn::Fields::Unit => quote! {},
                        }
                    };
                    quote! {Self::#ident #payload => {
                        #(let #fields = #fields.retype(retyper_instance););*
                        #item_ident::#ident #payload
                    }}
                })
                .collect();
            quote! {match self {
                #(#branches),*
            }}
        }
        Data::Struct(..) => unimplemented!(),
    };
    let mut wrapper_visitor = WrapperVisitor::default();
    wrapper_visitor.visit_derive_input(&input);
    let bounds = wrapper_visitor.types.iter().map(|ty| {
        let replace = |mut ty, to| {let mut visitor = TypeReplacer {from: parse_quote!{T}, to}; visitor.visit_type_mut(&mut ty); ty};
        let path_a: TypePath = parse_quote!(<RT::A as AstTypes>::dummy);
        let path_b: TypePath = parse_quote!(<RT::B as AstTypes>::dummy);
        let ty_a = replace(ty.clone(), path_a.qself.unwrap());
        let ty_b = replace(ty.clone(), path_b.qself.unwrap());
        quote!{<RT::A as AstTypes>::Wrapper<#ty_a>: Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<#ty_b>>}
    });
    let ts = quote! {

        impl<RT: AstRetyper> Retypable<RT> for #item_ident<RT::A>  where #(#bounds),* {
            type Out = #item_ident<RT::B>;
            fn retype(&self, retyper_instance: &RT) -> Self::Out {
                #body
            }
        }
    };
    panic!("{}", ts.to_token_stream());
    ts.into()
}
