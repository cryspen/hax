//! This module defines the `ImplFnDecoration` structure and utils
//! around it.

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

/// Calls `f` on the metas of `attrs`, descending into `cfg_attr(PRED, ..)`
/// wrappers: `f` receives the conjunction of the enclosing predicates, may
/// rewrite the meta in place, and returns whether to keep it.
pub fn retain_through_cfg_attr(
    attrs: &mut Vec<Attribute>,
    mut f: impl FnMut(&mut Meta, Option<&Meta>) -> bool,
) {
    attrs.retain_mut(|attr| retain_meta(&mut attr.meta, None, &mut f));
}

fn retain_meta(
    meta: &mut Meta,
    cfg: Option<Meta>,
    f: &mut impl FnMut(&mut Meta, Option<&Meta>) -> bool,
) -> bool {
    let Meta::List(ml) = meta else {
        return f(meta, cfg.as_ref());
    };
    if !ml.path.is_ident("cfg_attr") {
        return f(meta, cfg.as_ref());
    }
    let Ok(args) = ml.parse_args_with(punctuated::Punctuated::<Meta, Token![,]>::parse_terminated)
    else {
        return true;
    };
    let mut nested: Vec<Meta> = args.into_iter().collect();
    if nested.is_empty() {
        return true;
    }
    let pred = nested.remove(0);
    let cfg = Some(match cfg {
        Some(outer) => parse_quote! {all(#outer, #pred)},
        None => pred.clone(),
    });
    let len = nested.len();
    nested.retain_mut(|arg| retain_meta(arg, cfg.clone(), f));
    if len > 0 && nested.is_empty() {
        return false;
    }
    ml.tokens = quote! {#pred, #(#nested),*};
    true
}
