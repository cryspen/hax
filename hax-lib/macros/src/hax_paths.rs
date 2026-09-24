//! This module defines the `ImplFnDecoration` structure and utils
//! around it.

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

/// Whether `meta` is a `refine`, see [`expects_refine`].
pub fn is_refine(meta: &Meta) -> bool {
    matches!(meta, Meta::List(ml) if matches!(expects_refine(&ml.path), Ok(Some(_))))
}

/// Whether `meta` is an `order`, see [`expects_order`].
pub fn is_order(meta: &Meta) -> bool {
    matches!(meta, Meta::List(ml) if matches!(expects_order(&ml.path), Ok(Some(_))))
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
        let Meta::List(ml) = meta else {
            return f(meta, cfg);
        };
        if !ml.path.is_ident("cfg_attr") {
            return f(meta, cfg);
        }
        let Ok(args) =
            ml.parse_args_with(punctuated::Punctuated::<Meta, Token![,]>::parse_terminated)
        else {
            return true;
        };
        let mut args = args.into_iter();
        let Some(pred) = args.next() else {
            return true;
        };
        let nested_cfg: Meta = match cfg {
            Some(outer) => parse_quote! {all(#outer, #pred)},
            None => pred.clone(),
        };
        let nested: Vec<Meta> = args
            .filter_map(|mut meta| walk(&mut meta, Some(&nested_cfg), f).then_some(meta))
            .collect();
        ml.tokens = quote::quote! {#pred, #(#nested),*};
        !nested.is_empty()
    }
    attrs.retain_mut(|attr| walk(&mut attr.meta, None, &mut f));
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
