//! This module defines the `ImplFnDecoration` structure and utils
//! around it.

use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use syn::*;

fn expect_simple_path(path: &Path) -> Option<Vec<String>> {
    let mut chunks = vec![];
    if path.leading_colon.is_some() {
        chunks.push(String::new())
    }
    for segment in &path.segments {
        chunks.push(format!("{}", segment.ident));
        if !matches!(segment.arguments, PathArguments::None) {
            return None;
        }
    }
    Some(chunks)
}

/// The various strings allowed as decoration kinds.
pub const DECORATION_KINDS: &[&str] = &["decreases", "ensures", "ensures_ref", "requires"];

/// Expects a `Path` to be a decoration kind: `::hax_lib::<KIND>`,
/// `hax_lib::<KIND>` or `<KIND>` in (with `KIND` in
/// `DECORATION_KINDS`).
#[cfg(hax)]
pub fn expects_path_decoration(path: &Path) -> Result<Option<String>> {
    expects_hax_path(DECORATION_KINDS, path)
}

/// `meta` and its keyword, if it is a `KW(..)` hax attribute with `KW` in
/// `allowlist`, see [`expects_hax_path`].
pub fn as_hax_meta<'a>(meta: &'a Meta, allowlist: &[&str]) -> Option<(&'a MetaList, String)> {
    let Meta::List(ml) = meta else { return None };
    Some((ml, expects_hax_path(allowlist, &ml.path).ok()??))
}

/// Expects a `Path` to be a hax path: `::hax_lib::<KW>`,
/// `hax_lib::<KW>` or `<KW>` in (with `KW` in `allowlist`).
pub fn expects_hax_path(allowlist: &[&str], path: &Path) -> Result<Option<String>> {
    let path_span = path.span();
    let path = expect_simple_path(path)
        .ok_or_else(|| Error::new(path_span, "Expected a simple path, with no `<...>`."))?;
    Ok(
        match path
            .iter()
            .map(|x| x.as_str())
            .collect::<Vec<_>>()
            .as_slice()
        {
            [kw] | ["", "hax_lib", kw] | ["hax_lib", kw] if allowlist.contains(kw) => {
                Some(kw.to_string())
            }
            _ => None,
        },
    )
}

/// Pushes `meta` to `out`, splitting a `cfg_attr(PRED, ARGS..)` into one
/// entry per nested argument, under the conjunction of the predicates.
fn flatten_cfg_attr(meta: Meta, cfg: Option<Meta>, out: &mut Vec<(Option<Meta>, Meta)>) {
    let args = match &meta {
        Meta::List(ml) if ml.path.is_ident("cfg_attr") => ml
            .parse_args_with(punctuated::Punctuated::<Meta, Token![,]>::parse_terminated)
            .ok()
            // A malformed `cfg_attr(PRED)` is left for rustc to report.
            .filter(|args| args.len() > 1 || args.trailing_punct()),
        _ => None,
    };
    let Some(args) = args else {
        return out.push((cfg, meta));
    };
    let mut args = args.into_iter();
    let pred = args.next().unwrap();
    let cfg = Some(match cfg {
        Some(outer) => parse_quote! {all(#outer, #pred)},
        None => pred,
    });
    for arg in args {
        flatten_cfg_attr(arg, cfg.clone(), out);
    }
}

/// Calls `f` on the metas of `attrs`, splitting every `cfg_attr` into one
/// attribute per nested meta: `f` receives the conjunction of the enclosing
/// predicates, may rewrite the meta, and returns whether to keep it.
pub fn retain_through_cfg_attr(
    attrs: &mut Vec<Attribute>,
    mut f: impl FnMut(&mut Meta, Option<&Meta>) -> bool,
) {
    let mut kept = vec![];
    for attr in std::mem::take(attrs) {
        let mut metas = vec![];
        flatten_cfg_attr(attr.meta.clone(), None, &mut metas);
        for (cfg, mut meta) in metas {
            if !f(&mut meta, cfg.as_ref()) {
                continue;
            }
            let meta = match cfg {
                Some(cfg) => parse_quote! {cfg_attr(#cfg, #meta)},
                None => meta,
            };
            kept.push(Attribute {
                meta,
                ..attr.clone()
            });
        }
    }
    *attrs = kept;
}

/// Gates every item of `tokens` on `#[cfg(#pred)]`, if there is a `pred`.
pub fn cfg_gate(tokens: TokenStream, pred: Option<&Meta>) -> TokenStream {
    let Some(pred) = pred else {
        return tokens;
    };
    let Ok(file) = syn::parse2::<File>(tokens.clone()) else {
        return quote! {#[cfg(#pred)] const _: () = {#tokens};};
    };
    file.items
        .iter()
        .map(|item| quote! {#[cfg(#pred)] #item})
        .collect()
}

/// An item raising `error`, gated like [`cfg_gate`].
pub fn gated_error(error: Error, pred: Option<&Meta>) -> TokenStream {
    let error = error.to_compile_error();
    cfg_gate(quote! {const _: () = {#error};}, pred)
}

/// The error for an `order` on an unnamed field: constructors of unnamed
/// fields are positional, so reordering the fields of the type alone would be
/// ill-typed.
pub fn unnamed_order_error(order: &MetaList) -> Error {
    Error::new_spanned(order, "`order` is only supported on named fields.")
}

/// Drops the `refine`s of the fields of an enum or a union, raising an error
/// for each enabled one.
pub fn reject_non_struct_refines(item: &mut Item, errors: &mut Vec<TokenStream>) {
    let fields: Vec<&mut Field> = match item {
        Item::Enum(e) => e.variants.iter_mut().flat_map(|v| &mut v.fields).collect(),
        Item::Union(u) => u.fields.named.iter_mut().collect(),
        _ => return,
    };
    for field in fields {
        retain_through_cfg_attr(&mut field.attrs, |meta, cfg| {
            let Some((ml, _)) = as_hax_meta(meta, &["refine"]) else {
                return true;
            };
            let message = "`refine` is only supported on the fields of a struct.";
            errors.push(gated_error(Error::new_spanned(ml, message), cfg));
            false
        })
    }
}
