use std::collections::HashSet;

use quote::quote;
use syn::visit::Visit;
use syn::visit_mut::{self, VisitMut};
use syn::{
    Field, Fields, File, GenericParam, Generics, Ident, Item, ItemEnum, ItemMod, ItemStruct,
    TypePath,
};

use super::{collectors, utils};

/// Given an iterator of fields, this produces a vector of all its field idents.
/// When a field is not named, we produce a proper name.
pub fn field_idents<'a>(fields: impl Iterator<Item = &'a Field>) -> Vec<Ident> {
    fields
        .enumerate()
        .map(|(i, field)| {
            field.ident.clone().unwrap_or(Ident::new(
                &format!("anon_field_{i}"),
                proc_macro2::Span::call_site(),
            ))
        })
        .collect()
}

/// Produces enum or struct payloads given a value `Fields`.
/// For instance, given the fields `[x:T, y:U]` (e.g. a struct `S {x: T, y: U}`),
/// we produce `{x, y}`, and given [<anon>:T, <anon>:U] (e.g. a struct `S(T, U)`),
/// we produce `(anon_field_0, anon_field_1)`.
pub fn fields_to_payload(fields: &Fields) -> proc_macro2::TokenStream {
    let idents = field_idents(fields.iter());
    match fields {
        syn::Fields::Named(..) => quote! { { #(#idents),* } },
        syn::Fields::Unnamed(..) => quote! { ( #(#idents),* ) },
        syn::Fields::Unit => quote! {},
    }
}

/// Projects the identifier of a gtiven `Item`.
pub fn ident_of_item(item: &syn::Item) -> &syn::Ident {
    match item {
        Item::Struct(s) => &s.ident,
        Item::Enum(s) => &s.ident,
        _ => unimplemented!(),
    }
}

/// Projects the generics of a gtiven `Item`.
pub fn generics_of_item(item: &syn::Item) -> &syn::Generics {
    match item {
        Item::Struct(s) => &s.generics,
        Item::Enum(s) => &s.generics,
        _ => unimplemented!(),
    }
}

/// Prepend `origin` in front of every type path
pub struct PrefixOrigin;

impl VisitMut for PrefixOrigin {
    fn visit_type_path_mut(&mut self, type_path: &mut TypePath) {
        if type_path.qself.is_none() && type_path.path.segments.len() == 1 {
            type_path
                .path
                .segments
                .insert(0, syn::parse_quote! {origin});
        }
        visit_mut::visit_type_path_mut(self, type_path);
    }
}

/// Filters out any item which is not an enum, a struct or a type alias.
pub struct KeepStructsEnumsTyAliases;

impl VisitMut for KeepStructsEnumsTyAliases {
    fn visit_file_mut(&mut self, file: &mut File) {
        for item in &mut file.items {
            visit_mut::visit_item_mut(self, item);
        }
        file.items
            .retain(|item| matches!(item, Item::Struct(_) | Item::Enum(_) | Item::Type(_)));
    }

    fn visit_item_mod_mut(&mut self, item_mod: &mut ItemMod) {
        if let Some((_, items)) = &mut item_mod.content {
            for child in items.iter_mut() {
                visit_mut::visit_item_mut(self, child);
            }
            items.retain(|child| matches!(child, Item::Struct(_) | Item::Enum(_) | Item::Type(_)));
        }
    }
}

/// Remove a vector of unused lifetimes within a `Generics`.
fn prune_unused_lifetimes(generics: &mut Generics, used: &HashSet<syn::Ident>) {
    generics.params = generics
        .params
        .iter()
        .cloned()
        .filter(|param| match param {
            GenericParam::Lifetime(lf) => used.contains(&lf.lifetime.ident),
            _ => true,
        })
        .collect();
}

/// Remove unused lifetimes in structs or enums.
pub struct RemoveUnusedLifetimes;

impl VisitMut for RemoveUnusedLifetimes {
    fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
        let mut collector = collectors::LifetimeCollector::default();
        for field in &item_struct.fields {
            collector.visit_type(&field.ty);
        }
        utils::prune_unused_lifetimes(&mut item_struct.generics, &collector.used);
        visit_mut::visit_item_struct_mut(self, item_struct);
    }

    fn visit_item_enum_mut(&mut self, item_enum: &mut ItemEnum) {
        let mut collector = collectors::LifetimeCollector::default();
        for variant in &item_enum.variants {
            for field in &variant.fields {
                collector.visit_type(&field.ty);
            }
        }

        prune_unused_lifetimes(&mut item_enum.generics, &collector.used);
        visit_mut::visit_item_enum_mut(self, item_enum);
    }
}

/// Merge two `syn::Generics`, respecting lifetime orders
pub(crate) fn merge_generics(x: Generics, y: Generics) -> Generics {
    use itertools::Itertools;
    Generics {
        lt_token: x.lt_token.or(y.lt_token),
        gt_token: x.gt_token.or(y.gt_token),
        params: {
            let lts = x
                .lifetimes()
                .chain(y.lifetimes())
                .cloned()
                .map(GenericParam::Lifetime)
                .unique();
            let not_lts = x
                .params
                .clone()
                .into_iter()
                .filter(|p| !matches!(p, GenericParam::Lifetime(_)))
                .chain(
                    y.params
                        .clone()
                        .into_iter()
                        .filter(|p| !matches!(p, GenericParam::Lifetime(_))),
                )
                .unique();
            lts.chain(not_lts).collect()
        },
        where_clause: match (x.where_clause, y.where_clause) {
            (Some(wx), Some(wy)) => Some(syn::WhereClause {
                where_token: wx.where_token,
                predicates: wx
                    .predicates
                    .into_iter()
                    .chain(wy.predicates)
                    .unique()
                    .collect(),
            }),
            (Some(w), None) | (None, Some(w)) => Some(w),
            (None, None) => None,
        },
    }
}
