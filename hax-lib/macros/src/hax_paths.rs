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
pub fn expects_path_decoration(path: &Path) -> Result<Option<String>> {
    expects_hax_path(DECORATION_KINDS, path)
}

/// Whether `meta` is a decoration, see [`expects_path_decoration`].
pub fn is_decoration(meta: &Meta) -> bool {
    matches!(meta, Meta::List(ml) if matches!(expects_path_decoration(&ml.path), Ok(Some(_))))
}

/// `meta` if it is a `refine`, see [`expects_refine`].
pub fn as_refine(meta: &Meta) -> Option<&MetaList> {
    match meta {
        Meta::List(ml) if matches!(expects_refine(&ml.path), Ok(Some(_))) => Some(ml),
        _ => None,
    }
}

/// `meta` if it is an `order`, see [`expects_order`].
pub fn as_order(meta: &Meta) -> Option<&MetaList> {
    match meta {
        Meta::List(ml) if matches!(expects_order(&ml.path), Ok(Some(_))) => Some(ml),
        _ => None,
    }
}

/// Expects a path to be `[[::]hax_lib]::refine`
pub fn expects_refine(path: &Path) -> Result<Option<String>> {
    expects_hax_path(&["refine"], path)
}

/// Expects a path to be `[[::]hax_lib]::order`
pub fn expects_order(path: &Path) -> Result<Option<String>> {
    expects_hax_path(&["order"], path)
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

/// A `cfg_attr(PRED, ARGS..)`.
struct CfgAttr {
    pred: Meta,
    args: Vec<Meta>,
}

impl CfgAttr {
    fn parse(ml: &MetaList) -> Option<Self> {
        let mut args = ml
            .parse_args_with(punctuated::Punctuated::<Meta, Token![,]>::parse_terminated)
            .ok()?
            .into_iter();
        let pred = args.next()?;
        Some(CfgAttr {
            pred,
            args: args.collect(),
        })
    }

    /// The predicate under which the arguments are enabled, within `outer`.
    fn nested_cfg(&self, outer: Option<&Meta>) -> Meta {
        let pred = &self.pred;
        match outer {
            Some(outer) => parse_quote! {all(#outer, #pred)},
            None => pred.clone(),
        }
    }
}

fn as_cfg_attr(meta: &Meta) -> Option<&MetaList> {
    match meta {
        Meta::List(ml) if ml.path.is_ident("cfg_attr") => Some(ml),
        _ => None,
    }
}

/// Calls `f` on the metas of `attrs`, descending into `cfg_attr(PRED, ..)`
/// wrappers: `f` is then called on each nested meta, with the conjunction of
/// the enclosing predicates. `f` may rewrite a meta in place, and returns
/// whether to keep it. A `cfg_attr` left empty is dropped.
pub fn retain_through_cfg_attr(
    attrs: &mut Vec<Attribute>,
    mut f: impl FnMut(&mut Meta, Option<&Meta>) -> bool,
) {
    fn walk(
        meta: &mut Meta,
        cfg: Option<&Meta>,
        f: &mut impl FnMut(&mut Meta, Option<&Meta>) -> bool,
    ) -> bool {
        let Some(ml) = as_cfg_attr(meta) else {
            return f(meta, cfg);
        };
        let Some(cfg_attr) = CfgAttr::parse(ml) else {
            return true;
        };
        let nested_cfg = cfg_attr.nested_cfg(cfg);
        let mut changed = false;
        let mut kept = vec![];
        for mut meta in cfg_attr.args {
            let before = quote! {#meta}.to_string();
            if !walk(&mut meta, Some(&nested_cfg), f) {
                changed = true;
                continue;
            }
            changed |= quote! {#meta}.to_string() != before;
            kept.push(meta);
        }
        if let (true, Meta::List(ml)) = (changed, meta) {
            let pred = &cfg_attr.pred;
            ml.tokens = quote! {#pred, #(#kept),*};
        }
        !kept.is_empty()
    }
    attrs.retain_mut(|attr| walk(&mut attr.meta, None, &mut f));
}

/// Like [`retain_through_cfg_attr`], without rewriting anything.
#[cfg(hax)]
pub fn for_each_through_cfg_attr(attrs: &[Attribute], mut f: impl FnMut(&Meta, Option<&Meta>)) {
    fn walk(meta: &Meta, cfg: Option<&Meta>, f: &mut impl FnMut(&Meta, Option<&Meta>)) {
        let Some(ml) = as_cfg_attr(meta) else {
            return f(meta, cfg);
        };
        let Some(cfg_attr) = CfgAttr::parse(ml) else {
            return;
        };
        let nested_cfg = cfg_attr.nested_cfg(cfg);
        for meta in &cfg_attr.args {
            walk(meta, Some(&nested_cfg), f);
        }
    }
    for attr in attrs {
        walk(&attr.meta, None, &mut f);
    }
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

/// Like [`retain_through_cfg_attr`], keeping every meta.
#[cfg(hax)]
pub fn visit_through_cfg_attr(
    attrs: &mut Vec<Attribute>,
    mut f: impl FnMut(&mut Meta, Option<&Meta>),
) {
    retain_through_cfg_attr(attrs, |meta, cfg| {
        f(meta, cfg);
        true
    })
}
