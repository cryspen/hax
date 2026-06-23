mod hax_paths;

use hax_paths::*;
use proc_macro::{TokenStream, TokenTree};
use quote::quote;
use syn::{visit_mut::VisitMut, *};

macro_rules! identity_proc_macro_attribute {
    ($($name:ident),*$(,)?) => {
        $(
            #[proc_macro_attribute]
            pub fn $name(_attr: TokenStream, item: TokenStream) -> TokenStream {
                item
            }
        )*
    }
}

identity_proc_macro_attribute!(
    fstar_options,
    fstar_verification_status,
    include,
    exclude,
    requires,
    ensures,
    decreases,
    pv_inline,
    protocol_messages,
    process_init,
    process_write,
    process_read,
    opaque,
    opaque_type,
    transparent,
    refinement_type,
    fstar_replace,
    coq_replace,
    lean_replace,
    fstar_replace_body,
    coq_replace_body,
    lean_replace_body,
    fstar_before,
    coq_before,
    lean_before,
    fstar_after,
    coq_after,
    lean_after,
    fstar_smt_pat,
    fstar_postprocess_with,
    lean_proof,
    lean_pure_requires_proof,
    lean_pure_ensures_proof,
    lean_proof_method_grind,
    lean_proof_method_bv_decide,
);

// ---------------------------------------------------------------------------
// ProVerif `pv_*` / `proverif::*` macros (Aeneas/Charon path).
//
// This `dummy.rs` is the code that runs whenever `--cfg hax` is *not* set —
// i.e. both a normal `cargo build`/`test` of a client crate AND the
// charon/Aeneas ProVerif extraction (charon does not set `--cfg hax`). On the
// `--cfg hax` (OCaml hax-engine) path, `implementation.rs` runs instead.
//
// To make these annotations survive into the Aeneas Pure-IR, each lowers to an
// inert `#[cfg_attr(pv_extract, pv::<kind>(..))]` tool attribute. It is dropped
// by rustc on a normal build (`pv_extract` unset, so no `register_tool(pv)`
// needed); the charon dump step sets `--cfg pv_extract` + `register_tool(pv)`,
// so the attribute then survives to MIR as `AttrUnknown { path, args }` for the
// backend's `attrs.rs` to read. Arg shapes (M0 / M3 / M4):
//   - bare marker          → `#[pv::constructor]`        (args = None)
//   - `= "<text>"`         → `#[pv::handwritten = ".."]` (args = quoted string)
//   - `(text = "<text>")`  → `#[pv::before(text = "..")]`(args = `text = ".."`)
// `pv_inline` stays a plain identity above: on the Aeneas path it is blocked
// upstream (the closure→fn-ptr cast is an Aeneas `EError`), so emitting a
// `pv::inline` tool attribute would have nothing to act on.

/// A marker indicating a `fn` should be translated to a ProVerif constructor.
#[proc_macro_attribute]
pub fn pv_constructor(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: proc_macro2::TokenStream = item.into();
    quote! {
        #[allow(unexpected_cfgs)]
        #[cfg_attr(pv_extract, pv::constructor)]
        #item
    }
    .into()
}

/// A marker indicating a `fn` requires manual modelling in ProVerif (the bare
/// `pv::handwritten` makes the backend emit a `bitstring_default()` placeholder).
#[proc_macro_attribute]
pub fn pv_handwritten(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: proc_macro2::TokenStream = item.into();
    quote! {
        #[allow(unexpected_cfgs)]
        #[cfg_attr(pv_extract, pv::handwritten)]
        #item
    }
    .into()
}

/// Model a `fn` as a single opaque `extern__<fn>` letfun of uniform-bitstring
/// arity: declare the symbol (`pv::before`) and call it from the body
/// (`pv::handwritten`). Mirrors `implementation.rs`'s `pv_extern`.
#[proc_macro_attribute]
pub fn pv_extern(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let fn_name = item.sig.ident.to_string();
    let arity = item.sig.inputs.len();
    let arg_names: Vec<String> = item
        .sig
        .inputs
        .iter()
        .enumerate()
        .map(|(i, arg)| match arg {
            FnArg::Receiver(_) => "self".to_string(),
            FnArg::Typed(pat_type) => match &*pat_type.pat {
                Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
                _ => format!("p{}", i),
            },
        })
        .collect();
    let bitstring_args = std::iter::repeat("bitstring")
        .take(arity)
        .collect::<Vec<_>>()
        .join(", ");
    let decl = format!("fun extern__{fn_name}({bitstring_args}): bitstring.");
    let body_call = format!("extern__{fn_name}({})", arg_names.join(", "));
    quote! {
        #[allow(unexpected_cfgs)]
        #[cfg_attr(pv_extract, pv::before(text = #decl))]
        #[cfg_attr(pv_extract, pv::handwritten(text = #body_call))]
        #item
    }
    .into()
}

/// Shorthand for `pv::handwritten = "<lit>"` — a trivial constant/body stub.
#[proc_macro_attribute]
pub fn pv_stub(attr: TokenStream, item: TokenStream) -> TokenStream {
    let payload: proc_macro2::TokenStream = attr.into();
    let item: proc_macro2::TokenStream = item.into();
    quote! {
        #[allow(unexpected_cfgs)]
        #[cfg_attr(pv_extract, pv::handwritten(text = #payload))]
        #item
    }
    .into()
}

/// Declare this letfun as the (one-sided) inverse of another function via a
/// `reduc` rule, emitted verbatim. Mirrors `implementation.rs`'s `pv_inverse_of`.
#[proc_macro_attribute]
pub fn pv_inverse_of(attr: TokenStream, item: TokenStream) -> TokenStream {
    let other_path = parse_macro_input!(attr as syn::Path);
    let other_str = quote! { #other_path }.to_string().replace(' ', "");
    let item_fn: ItemFn = parse_macro_input!(item);
    let self_name = item_fn.sig.ident.to_string();
    let body = format!("reduc forall x: bitstring; ${{{self_name}}}(${{{other_str}}}(x)) = x.");
    quote! {
        #[allow(unexpected_cfgs)]
        #[cfg_attr(pv_extract, pv::verbatim(text = #body))]
        #item_fn
    }
    .into()
}

// All four lower to the delimited `pv::<kind>(text = "…")` shape: charon reads
// delimited args token-wise (works for macro-synthesized literals), whereas the
// `= "…"` shape is read from the source span and breaks for synthesized text.
// The backend's `attr_text` accepts either shape, so this is uniform.
macro_rules! proverif_quoting_dummy {
    ($name:ident, $kind:ident) => {
        #[proc_macro_attribute]
        pub fn $name(payload: TokenStream, item: TokenStream) -> TokenStream {
            let payload: proc_macro2::TokenStream = payload.into();
            let item: proc_macro2::TokenStream = item.into();
            quote! {
                #[allow(unexpected_cfgs)]
                #[cfg_attr(pv_extract, pv::$kind(text = #payload))]
                #item
            }
            .into()
        }
    };
}

proverif_quoting_dummy!(proverif_before, before);
proverif_quoting_dummy!(proverif_after, after);
proverif_quoting_dummy!(proverif_replace, verbatim);
proverif_quoting_dummy!(proverif_replace_body, handwritten);

#[proc_macro]
pub fn fstar_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn coq_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn lean_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn proverif_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}

#[proc_macro_attribute]
pub fn lemma(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote! {}.into()
}

fn unsafe_expr() -> TokenStream {
    // `*_unsafe_expr("<code>")` are macro generating a Rust expression of any type, that will be replaced by `<code>` in the backends.
    // This should be used solely in hax-only contextes.
    // If this macro is used, that means the user broke this rule.
    quote! { ::std::compile_error!("`hax_lib::unsafe_expr` has no meaning outside of hax extraction, please use it solely on hax-only places.") }.into()
}

#[proc_macro]
pub fn fstar_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn coq_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn lean_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn proverif_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}

#[proc_macro]
pub fn fstar_prop_expr(_payload: TokenStream) -> TokenStream {
    quote! {::hax_lib::Prop::from_bool(true)}.into()
}
#[proc_macro]
pub fn coq_prop_expr(_payload: TokenStream) -> TokenStream {
    quote! {::hax_lib::Prop::from_bool(true)}.into()
}
#[proc_macro]
pub fn lean_prop_expr(_payload: TokenStream) -> TokenStream {
    quote! {::hax_lib::Prop::from_bool(true)}.into()
}
#[proc_macro]
pub fn proverif_prop_expr(_payload: TokenStream) -> TokenStream {
    quote! {::hax_lib::Prop::from_bool(true)}.into()
}

fn not_hax_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !matches!(expects_path_decoration(&ml.path), Ok(Some(_)))
    } else {
        true
    }
}

fn not_field_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !(matches!(expects_refine(&ml.path), Ok(Some(_)))
            || matches!(expects_order(&ml.path), Ok(Some(_))))
    } else {
        true
    }
}

#[proc_macro_attribute]
pub fn attributes(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: Item = parse_macro_input!(item);

    struct AttrVisitor;

    use syn::visit_mut;
    impl VisitMut for AttrVisitor {
        fn visit_item_trait_mut(&mut self, item: &mut ItemTrait) {
            for ti in item.items.iter_mut() {
                if let TraitItem::Fn(fun) = ti {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_trait_mut(self, item);
        }
        fn visit_type_mut(&mut self, _type: &mut Type) {}
        fn visit_item_impl_mut(&mut self, item: &mut ItemImpl) {
            for ii in item.items.iter_mut() {
                if let ImplItem::Fn(fun) = ii {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_impl_mut(self, item);
        }
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);

            match item {
                Item::Struct(s) => {
                    for field in s.fields.iter_mut() {
                        field.attrs.retain(not_field_attribute)
                    }
                }
                _ => (),
            }
        }
    }

    let mut item = item;
    AttrVisitor.visit_item_mut(&mut item);

    quote! { #item }.into()
}

#[proc_macro]
pub fn int(payload: TokenStream) -> TokenStream {
    let mut tokens = payload.into_iter().peekable();
    let negative = matches!(tokens.peek(), Some(TokenTree::Punct(p)) if p.as_char() == '-');
    if negative {
        tokens.next();
    }
    let [lit @ TokenTree::Literal(_)] = &tokens.collect::<Vec<_>>()[..] else {
        return quote! { ::std::compile_error!("Expected exactly one numeric literal") }.into();
    };
    let lit: proc_macro2::TokenStream = TokenStream::from(lit.clone()).into();
    quote! {::hax_lib::int::Int(#lit)}.into()
}

#[proc_macro_attribute]
pub fn impl_fn_decoration(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote! { ::std::compile_error!("`impl_fn_decoration` is an internal macro and should never be used directly.") }.into()
}

#[proc_macro_attribute]
pub fn trait_fn_decoration(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote! { ::std::compile_error!("`trait_fn_decoration` is an internal macro and should never be used directly.") }.into()
}

#[proc_macro]
pub fn loop_invariant(_predicate: TokenStream) -> TokenStream {
    quote! {}.into()
}

#[proc_macro]
pub fn loop_decreases(_predicate: TokenStream) -> TokenStream {
    quote! {}.into()
}
