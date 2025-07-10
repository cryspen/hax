use quote::{quote, ToTokens};
use std::{fs, path::Path};
use syn::{parse_file, Field, Fields, File, GenericParam, Generics, Ident};

/// Given an iterator of fields, this produces a vector of all its field idents.
/// When a field is not named, we produce a proper name.
pub(crate) fn field_typed_idents<'a>(
    fields: impl Iterator<Item = &'a Field>,
) -> Vec<(Ident, syn::Type)> {
    fields
        .enumerate()
        .map(|(i, field)| {
            (
                field.ident.clone().unwrap_or(Ident::new(
                    &format!("anon_field_{i}"),
                    proc_macro2::Span::call_site(),
                )),
                field.ty.clone(),
            )
        })
        .collect()
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

/// Given an iterator of fields, this produces a vector of all its field idents.
/// When a field is not named, we produce a proper name.
pub(crate) fn field_idents<'a>(fields: impl Iterator<Item = &'a Field>) -> Vec<Ident> {
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
pub(crate) fn fields_to_payload(fields: &Fields) -> proc_macro2::TokenStream {
    let idents = field_idents(fields.iter());
    match fields {
        syn::Fields::Named(..) => quote! { { #(#idents),* } },
        syn::Fields::Unnamed(..) => quote! { ( #(#idents),* ) },
        syn::Fields::Unit => quote! {},
    }
}

/// Write and format a Rust module
pub(crate) fn write(file: &impl ToTokens, path: &str) {
    let out_path = Path::new(path);
    fs::write(&out_path, format!("{}", file.to_token_stream()))
        .expect(&format!("Failed to write `{}`", path));
    std::process::Command::new("rustfmt")
        .arg(&out_path)
        .status()
        .expect("failed to run rustfmt");
}

/// Reads a file and parses it as a syn `File`
pub(crate) fn read(path: &str) -> File {
    let src_path = Path::new(path);
    let contents = fs::read_to_string(&src_path).expect(&format!("Failed to read `{}`", path));
    parse_file(&contents).expect(&format!("Failed to parse `{}` as a Rust file", path))
}
