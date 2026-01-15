use crate::{make_fn_decoration, prelude::*, unified_macros::WithEnvPayload, FnDecorationKind};

/// Add a logical precondition to a function.
// Note you can use the `forall` and `exists` operators. (TODO: commented out for now, see #297)
/// In the case of a function that has one or more `&mut` inputs, in
/// the `ensures` clause, you can refer to such an `&mut` input `x` as
/// `x` for its "past" value and `future(x)` for its "future" value.
///
/// You can use the (unqualified) macro `fstar!` (`BACKEND!` for any
/// backend `BACKEND`) to inline F* (or Coq, ProVerif, etc.) code in
/// the precondition, e.g. `fstar!("true")`.
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[requires(x.len() == y.len())]
// #[requires(x.len() == y.len() && forall(|i: usize| i >= x.len() || y[i] > 0))] (TODO: commented out for now, see #297)
/// pub fn div_pairwise(x: Vec<u64>, y: Vec<u64>) -> Vec<u64> {
///     x.iter()
///         .copied()
///         .zip(y.iter().copied())
///         .map(|(x, y)| x / y)
///         .collect()
/// }
/// ```

// #[proc_macro_attribute]
pub fn requires(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let WithEnvPayload {
        env_payload,
        value: phi,
    }: WithEnvPayload<syn::Expr> = parse_macro_input!(attr);
    let item: FnLike = parse_macro_input!(item);
    let env = env_payload.unwrap_or_default().env() + item.sig.generics.clone();
    let (requires, attr) = make_fn_decoration(
        phi.clone(),
        item.sig.clone(),
        FnDecorationKind::Requires,
        env.generics,
        env.self_type,
    );
    let mut item_with_debug = item.clone();
    item_with_debug
        .block
        .stmts
        .insert(0, parse_quote! {debug_assert!(#phi);});
    quote! {
        #requires
        #attr
        #item
    }
    .into()
}
