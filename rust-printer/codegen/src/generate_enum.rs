//! Provides the `FragmentEnumGenerator` helper struct

use crate::visitors;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{parse_quote, File, Generics, Ident, Item};

/// Helper struct to generate enums out of datatypes.
///
/// Given `file` that contains a list of datatypes `T1`...`TN`, this helps producing
/// an enum named `name` with variants `T1(T1)`, `T2(T2)`, ..., `TN(TN)`.
/// Also generate `From` instances lifiting `T1`..`TN` to the generated enum `name`.
///
/// This takes into account lifetimes and type parameters of `T1`...`TN`.
///
/// If `owned` is false, then the variants will hold references, e.g. be of the shape `T1(&'lt T1)`.
#[derive(Clone, Copy)]
pub struct FragmentEnumGenerator<'a> {
    /// The name of the `enum` to generate
    pub enum_name: &'a str,
    /// The (syn) `File` that contains the datatypes
    pub file: &'a File,
    /// Shall we produce an owned version of the enum?
    pub owned: bool,
    /// Extra variants
    pub extra_variants: &'a TokenStream,
    /// Extra attributes
    pub extra_attributes: &'a TokenStream,
}

impl<'a> FragmentEnumGenerator<'a> {
    /// Extract a list of the identifier and generics of the datatypes held in `File`.
    fn datatypes(self) -> Vec<(&'a Ident, &'a Generics)> {
        self.file
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Struct(s) => Some((&s.ident, &s.generics)),
                Item::Enum(s) => Some((&s.ident, &s.generics)),
                _ => None,
            })
            .collect()
    }
    /// Produces a clause that contains all the generics any datatype may
    /// require, plus an extra lifetime `'lt` in case we're producing a borrowed
    /// version of an enum.
    fn generics(self) -> Generics {
        self.datatypes()
            .iter()
            .map(|(_, g)| *g)
            .cloned()
            .chain(self.borrowed().then_some(parse_quote! {<'lt>}))
            .reduce(visitors::utils::merge_generics)
            .unwrap_or(parse_quote! {})
    }
    /// Are we produced a enum with borrowed fragment?
    fn borrowed(self) -> bool {
        !self.owned
    }
    /// `None` if owned, `Some('lt)` otherwise
    fn lifetime_token(self) -> Option<TokenStream> {
        self.borrowed().then_some(quote! {&'lt})
    }
    fn enum_ident(self) -> Ident {
        Ident::new(self.enum_name, Span::call_site())
    }
    /// Produces variants
    fn variants(self) -> Vec<TokenStream> {
        let lt = self.lifetime_token();
        self.datatypes()
            .iter()
            .map(|(ident, generics)| quote! {#ident(#lt #ident #generics)})
            .collect()
    }
    /// Produces `into` instances from each datatype in `self.file` to the enum
    fn into_instances(self) -> Vec<TokenStream> {
        let lt = self.lifetime_token();
        let merged_generics = self.generics();
        let enum_ident = self.enum_ident();
        self.datatypes()
            .iter()
            .map(|(ident, generics)| {
                quote! {
                    impl #merged_generics From<#lt #ident #generics> for #enum_ident #merged_generics {
                        fn from(item: #lt #ident #generics) -> Self {
                            Self::#ident(item)
                        }
                    }
                }
            })
            .collect()
    }

    /// Generate a `File` containing the `enum` and the `Into` instances
    pub fn to_file(self) -> File {
        let variants = self.variants();
        let into_instances = self.into_instances();
        let generics = self.generics();
        let ident = self.enum_ident();
        let Self {
            extra_attributes,
            extra_variants,
            ..
        } = self;
        parse_quote! {
            #[allow(missing_docs)]
            #extra_attributes
            pub enum #ident #generics {
                #(#variants,)*
                #extra_variants
            }

            #(#into_instances)*
        }
    }
}
