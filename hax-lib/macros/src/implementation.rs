//! Implementations of the proc-macros that are too big to sit next to their
//! documentation in `lib.rs`, and the machinery they share.

use crate::impl_fn_decoration::*;
use crate::prelude::*;
use crate::rewrite_self::SelfProjection;
use crate::utils::*;

/// Reports a compile error at `$span` and returns from the enclosing
/// proc-macro function. The message is either a single value or a `format!`
/// string with arguments. `$span` may be a `proc_macro::Span` or a
/// `proc_macro2::Span`.
macro_rules! abort {
    ($span:expr, $fmt:literal, $($arg:expr),+ $(,)?) => {
        return ::syn::Error::new($span.into(), format!($fmt, $($arg),+))
            .to_compile_error()
            .into()
    };
    ($span:expr, $msg:expr $(,)?) => {
        return ::syn::Error::new($span.into(), $msg)
            .to_compile_error()
            .into()
    };
}

/// Like [`abort!`], but reports the error at the macro call site.
macro_rules! abort_call_site {
    ($fmt:literal, $($arg:expr),+ $(,)?) => {
        return ::syn::Error::new(::proc_macro2::Span::call_site(), format!($fmt, $($arg),+))
            .to_compile_error()
            .into()
    };
    ($msg:expr $(,)?) => {
        return ::syn::Error::new(::proc_macro2::Span::call_site(), $msg)
            .to_compile_error()
            .into()
    };
}

pub fn loop_invariant(predicate: pm::TokenStream) -> pm::TokenStream {
    let predicate2: TokenStream = predicate.clone().into();
    let predicate_expr: syn::Expr = parse_macro_input!(predicate);

    let (invariant_f, predicate) = match predicate_expr {
        syn::Expr::Closure(_) => (quote!(hax_lib::_internal_loop_invariant), predicate2),
        _ => (
            quote!(hax_lib::_internal_while_loop_invariant),
            quote!(::hax_lib::Prop::from(#predicate2)),
        ),
    };
    let ts: pm::TokenStream = quote! {
        #[cfg(#HaxCfgOptionName)]
        {
            #invariant_f({
                #HaxQuantifiers
                #predicate
            })
        }
    }
    .into();
    ts
}

pub fn loop_decreases(predicate: pm::TokenStream) -> pm::TokenStream {
    let predicate: TokenStream = predicate.into();
    let ts: pm::TokenStream = quote! {
        #[cfg(#HaxCfgOptionName)]
        {
            hax_lib::_internal_loop_decreases({
                #HaxQuantifiers
                use ::hax_lib::int::ToInt;
                (#predicate).to_int()
            })
        }
    }
    .into();
    ts
}

pub fn fstar_verification_status(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let action = format!("{}", parse_macro_input!(attr as Ident));
    match action.as_str() {
        "lax" => {
            let item: TokenStream = item.into();
            quote! {
                #[::hax_lib::fstar::options("--admit_smt_queries true")]
                #item
            }
        }
        "panic_free" => {
            let mut item = parse_macro_input!(item as FnLike);
            if let Some(last) = item
                .block
                .stmts
                .iter_mut()
                .rev()
                .find(|stmt| matches!(stmt, syn::Stmt::Expr(_, None)))
                .as_mut()
            {
                **last = syn::Stmt::Expr(
                    parse_quote! {
                        {let result = #last;
                        ::hax_lib::fstar!("_hax_panic_freedom_admit_");
                         result}
                    },
                    None,
                );
            } else {
                item.block.stmts.push(syn::Stmt::Expr(
                    parse_quote! {::hax_lib::fstar!("_hax_panic_freedom_admit_")},
                    None,
                ));
            }
            quote! {
                #item
            }
        }
        _ => abort_call_site!("Expected `lax` or `panic_free`"),
    }
    .into()
}

/*
TODO: no support in any backends (see #297)

/// Exclude this item from the Hax translation, and replace it with a
/// axiomatized model in each backends. The path of the axiomatized
/// model should be given in Rust syntax.
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[modeled_by(FStar::IO::debug_print_string)]
/// fn f(line: String) {
///   println!("{}", line)
/// }
/// ```
#[proc_macro_attribute]
pub fn modeled_by(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    use quote::ToTokens;
    let model_path = parse_macro_input!(attr as syn::Path).to_token_stream();
    let item: TokenStream = item.into();
    let attr = AttrPayload::ItemStatus(ItemStatus::Excluded {
        modeled_by: Some(model_path.to_string()),
    });
    quote! {#attr #item}.into()
}
*/

pub fn lemma(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let mut item: syn::ItemFn = parse_macro_input!(item as ItemFn);
    use syn::{GenericArgument, PathArguments, ReturnType, spanned::Spanned};

    fn add_allow_unused_variables_to_args(func: &mut syn::ItemFn) {
        let attr: syn::Attribute = parse_quote!(#[allow(unused_variables)]);

        for input in &mut func.sig.inputs {
            if let FnArg::Typed(pat_type) = input {
                pat_type.attrs.push(attr.clone());
            }
        }
    }

    /// Parses a `syn::Type` of the shape `Proof<{FORMULA}>`.
    fn parse_proof_type(r#type: syn::Type) -> Option<syn::Expr> {
        let syn::Type::Path(syn::TypePath {
            qself: None,
            path:
                syn::Path {
                    leading_colon: None,
                    segments,
                },
        }) = r#type
        else {
            return None;
        };
        let ps = (segments.len() == 1).then_some(()).and(segments.first())?;
        (ps.ident == "Proof").then_some(())?;
        let PathArguments::AngleBracketed(args) = &ps.arguments else {
            None?
        };
        let args = args.args.clone();
        let GenericArgument::Const(e) = (args.len() == 1).then_some(()).and(args.first())? else {
            None?
        };
        Some(e.clone())
    }
    let _ = parse_macro_input!(attr as parse::Nothing);
    let attr = &AttrPayload::Lemma;
    add_allow_unused_variables_to_args(&mut item);
    if let ReturnType::Type(_, r#type) = &item.sig.output {
        if let Some(ensures_clause) = parse_proof_type(*r#type.clone()) {
            use AttrPayload::NeverErased;
            item.sig.output = ReturnType::Default;
            return ensures(
                quote! {|_| #ensures_clause}.into(),
                quote! { #attr #NeverErased #item }.into(),
            );
        }
    }

    abort!(
        item.sig.output.span(),
        "A lemma is expected to return a `Proof<{STATEMENT}>`, where {STATEMENT} is a `Prop` expression."
    )
}

pub fn ensures(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let ExprClosure1 {
        arg: ret_binder,
        body: phi,
    } = parse_macro_input!(attr);
    let item: FnLike = parse_macro_input!(item);
    let kind = FnDecorationKind::Ensures {
        ret_binder: ret_binder.clone(),
    };
    let (ensures, attr) = make_fn_decoration(
        phi.clone(),
        item.sig.clone(),
        kind,
        None,
        None,
        SelfProjection::Unknown,
    );
    let mut item_with_debug = item.clone();
    let body = item.block.clone();
    item_with_debug.block.stmts =
        parse_quote!(let #ret_binder = #body; debug_assert!(#phi); #ret_binder);
    quote! {
        #ensures #attr
        // TODO: disable `assert!`s for now (see #297)
        #item
        // #[cfg(    all(not(#HaxCfgOptionName),     debug_assertions )) ] #item_with_debug
        // #[cfg(not(all(not(#HaxCfgOptionName),     debug_assertions )))] #item
    }
    .into()
}

mod kw {
    syn::custom_keyword!(hax_lib);
    syn::custom_keyword!(decreases);
    syn::custom_keyword!(ensures);
    syn::custom_keyword!(requires);
    syn::custom_keyword!(refine);
}

pub fn impl_fn_decoration(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let ImplFnDecoration {
        kind,
        phi,
        generics,
        self_ty,
        self_trait,
    } = parse_macro_input!(attr);
    let mut item: FnLike = parse_macro_input!(item);
    let projection = match self_trait {
        Some(trait_) => SelfProjection::Trait(trait_),
        None => SelfProjection::Unknown,
    };
    let (decoration, attr) = make_fn_decoration(
        phi,
        item.sig.clone(),
        kind,
        Some(generics),
        Some(self_ty),
        projection,
    );
    let decoration = Stmt::Item(Item::Verbatim(decoration));
    item.block.stmts.insert(0, decoration);
    quote! {#attr #item}.into()
}

pub fn trait_fn_decoration(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let ImplFnDecoration {
        kind,
        phi,
        generics,
        self_ty,
        self_trait,
    } = parse_macro_input!(attr);
    let mut item: syn::TraitItemFn = parse_macro_input!(item);
    let projection = match self_trait {
        Some(_) => SelfProjection::Unsupported,
        None => SelfProjection::Unknown,
    };
    let (decoration, attr) = make_fn_decoration(
        phi,
        item.sig.clone(),
        kind,
        Some(generics),
        Some(self_ty),
        projection,
    );
    let decoration = Stmt::Item(Item::Verbatim(decoration));
    item.sig
        .generics
        .where_clause
        .get_or_insert(parse_quote! {where})
        .predicates
        .push(parse_quote! {[(); {#decoration 0}]:});
    quote! {#attr #item}.into()
}

pub fn attributes(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: Item = parse_macro_input!(item);

    #[derive(Default)]
    struct AttrVisitor {
        extra_items: Vec<TokenStream>,
    }

    use syn::visit_mut;
    impl VisitMut for AttrVisitor {
        fn visit_item_trait_mut(&mut self, item: &mut ItemTrait) {
            let span = item.span();
            let self_trait = self_trait_path(item);
            let (trait_generics, supertraits) = (item.generics.clone(), item.supertraits.clone());
            for ti in item.items.iter_mut() {
                if let TraitItem::Fn(fun) = ti {
                    let sig = fun.sig.clone();
                    let extra_items = &mut self.extra_items;
                    for attr in &mut fun.attrs {
                        visit_meta_through_cfg_attr(&mut attr.meta, None, &mut |meta, cfg| {
                            let Meta::List(ml) = meta else { return };
                            let Ok(Some(decoration)) = expects_path_decoration(&ml.path) else {
                                return;
                            };
                            let decoration = syn::Ident::new(&decoration, ml.path.span());

                            let mut generics = trait_generics.clone();
                            // `Self_` needs the trait itself among its bounds, not
                            // just the supertraits, else `Self::Assoc` has nothing
                            // to resolve against (#2089).
                            let mut bounds = supertraits.clone();
                            bounds.push(TypeParamBound::Trait(TraitBound {
                                paren_token: None,
                                modifier: TraitBoundModifier::None,
                                lifetimes: None,
                                path: self_trait.clone(),
                            }));
                            let predicate = WherePredicate::Type(PredicateType {
                                lifetimes: None,
                                bounded_ty: parse_quote! {Self_},
                                colon_token: Token![:](span),
                                bounds,
                            });
                            let mut where_clause = generics
                                .where_clause
                                .clone()
                                .unwrap_or(parse_quote! {where});
                            where_clause.predicates.push(predicate);
                            generics.where_clause = Some(where_clause);
                            let self_ty: Type = parse_quote! {Self_};
                            let tokens = ml.tokens.clone();
                            let generics = merge_generics(parse_quote! {<Self_>}, generics);
                            let ImplFnDecoration {
                                kind, phi, self_ty, ..
                            } = parse_quote! {#decoration, #generics, where, #self_ty, #tokens};
                            let (decoration, relation_attr) = make_fn_decoration(
                                phi,
                                sig.clone(),
                                kind,
                                Some(generics),
                                Some(self_ty),
                                SelfProjection::TypeParam,
                            );
                            // Replacing the meta (and not the whole attribute) keeps any
                            // enclosing `cfg_attr` wrapper: the relation attribute and the
                            // sibling item below appear under the very same conditions.
                            let relation_attr: Attribute = parse_quote! {#relation_attr};
                            *meta = relation_attr.meta;
                            extra_items.push(match cfg {
                                Some(pred) => cfg_gate(decoration, pred),
                                None => decoration,
                            });
                        });
                    }
                }
            }
            visit_mut::visit_item_trait_mut(self, item);
        }
        fn visit_type_mut(&mut self, _type: &mut Type) {}
        fn visit_item_impl_mut(&mut self, item: &mut ItemImpl) {
            let (generics, self_ty) = (item.generics.clone(), item.self_ty.clone());
            // The trait implemented by this block, if any: it qualifies the
            // `Self::Assoc` projections of the decorated methods.
            let as_trait = item
                .trait_
                .as_ref()
                .and_then(|(not, path, _)| not.is_none().then(|| quote! {as #path}));
            // Only the associated types this block defines can be qualified.
            let assoc: Vec<String> = item
                .items
                .iter()
                .filter_map(|item| match item {
                    ImplItem::Type(ty) => Some(ty.ident.to_string()),
                    _ => None,
                })
                .collect();
            for ii in item.items.iter_mut() {
                if let ImplItem::Fn(fun) = ii {
                    let decorated = fun.attrs.iter().any(|attr| {
                        matches!(&attr.meta, Meta::List(ml)
                            if matches!(expects_path_decoration(&ml.path), Ok(Some(_))))
                    });
                    if decorated {
                        if let Some(error) = foreign_self_projection_error(&fun.sig, &assoc) {
                            // Drop the specifications: generating them would
                            // pile rustc errors on top of ours.
                            fun.attrs.retain(|attr| match &attr.meta {
                                Meta::List(ml) => {
                                    !matches!(expects_path_decoration(&ml.path), Ok(Some(_)))
                                }
                                _ => true,
                            });
                            self.extra_items.push(error);
                            continue;
                        }
                    }
                    for attr in fun.attrs.iter_mut() {
                        visit_meta_through_cfg_attr(&mut attr.meta, None, &mut |meta, _cfg| {
                            let Meta::List(ml) = meta else { return };
                            let Ok(Some(decoration)) = expects_path_decoration(&ml.path) else {
                                return;
                            };
                            let decoration = syn::Ident::new(&decoration, ml.path.span());
                            let tokens = ml.tokens.clone();
                            ml.tokens = impl_fn_decoration_args(
                                &decoration,
                                &generics,
                                &self_ty,
                                &as_trait,
                                &tokens,
                            );
                            ml.path = parse_quote! {::hax_lib::impl_fn_decoration};
                        });
                    }
                }
            }
            visit_mut::visit_item_impl_mut(self, item);
        }
        fn visit_fields_named_mut(&mut self, fields_named: &mut FieldsNamed) {
            visit_mut::visit_fields_named_mut(self, fields_named);

            fn handle_reorder_attribute(attrs: &mut [Attribute], errors: &mut Vec<TokenStream>) {
                let Some((attr, order)) = attrs.iter_mut().find_map(|attr| {
                    if let Ok(Some(_)) = expects_order(attr.path()) {
                        let lit: LitInt = attr.parse_args().ok()?;
                        Some((attr, lit))
                    } else {
                        None
                    }
                }) else {
                    return;
                };

                let Ok(n) = order.base10_parse() else {
                    errors.push(parse_quote!{const _: () = {compile_error!("Expected a (base 10) i32 literal.")};});
                    return;
                };
                let payload = AttrPayload::Order(n);
                *attr = parse_quote!(#payload);
            }

            for field in &mut fields_named.named {
                handle_reorder_attribute(&mut field.attrs, &mut self.extra_items);
            }
        }
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);

            let mut extra: Vec<Item> = vec![];
            match item {
                Item::Struct(s) => {
                    let only_one_field = s.fields.len() == 1;
                    // The generated `refinement` functions need the generics of
                    // the struct in scope: a field type may mention a generic
                    // parameter (e.g. a `const LEN: usize` used in `[u8; LEN]`).
                    // We strip any defaults since those are not allowed on
                    // function generics. Unused generics are fine on functions.
                    let generics = {
                        let mut generics = s.generics.clone();
                        for param in generics.params.iter_mut() {
                            match param {
                                GenericParam::Type(p) => {
                                    p.eq_token = None;
                                    p.default = None;
                                }
                                GenericParam::Const(p) => {
                                    p.eq_token = None;
                                    p.default = None;
                                }
                                GenericParam::Lifetime(_) => {}
                            }
                        }
                        generics
                    };
                    let where_clause = generics.where_clause.clone();
                    let idents: Vec<_> = s
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            let ident = field.ident.clone().unwrap_or(if only_one_field {
                                format_ident!("x")
                            } else {
                                format_ident!("x{}", i)
                            });
                            (ident, field.ty.clone())
                        })
                        .collect();
                    for (i, field) in s.fields.iter_mut().enumerate() {
                        let prev = &idents[0..=i];
                        let refine: Option<(&mut Attribute, Expr)> =
                            field.attrs.iter_mut().find_map(|attr| {
                                if let Ok(Some(_)) = expects_refine(attr.path()) {
                                    let payload = attr.parse_args().ok()?;
                                    Some((attr, payload))
                                } else {
                                    None
                                }
                            });
                        if let Some((attr, refine)) = refine {
                            let binders: TokenStream = prev
                                .iter()
                                .map(|(name, ty)| quote! {#name: #ty, })
                                .collect();
                            let uid = ItemUid::fresh();
                            let uid_attr = AttrPayload::Uid(uid.clone());
                            let assoc_attr = AttrPayload::AssociatedItem {
                                role: AssociationRole::Refine,
                                item: uid,
                            };
                            *attr = syn::parse_quote! { #assoc_attr };
                            let status_attr =
                                &AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
                            extra.push(syn::parse_quote! {
                                #[cfg(#HaxCfgOptionName)]
                                #status_attr
                                const _: () = {
                                    #uid_attr
                                    #status_attr
                                    fn refinement #generics (#binders) -> ::hax_lib::Prop #where_clause { ::hax_lib::Prop::from(#refine) }
                                };
                            })
                        }
                    }
                }
                _ => (),
            }
            let extra: TokenStream = extra.iter().map(|extra| quote! {#extra}).collect();
            *item = Item::Verbatim(quote! {#extra #item});
        }
    }

    let mut v = AttrVisitor::default();
    let mut item = item;
    v.visit_item_mut(&mut item);
    let extra_items = v.extra_items;

    quote! { #item #(#extra_items)* }.into()
}

pub fn opaque_type(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    opaque(attr, item)
}

pub fn opaque(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: Item = parse_macro_input!(item);
    let attr = AttrPayload::Erased;
    let charon = charon_attr(quote! {opaque});
    quote! {#attr #charon #item}.into()
}

pub fn int(payload: pm::TokenStream) -> pm::TokenStream {
    let n: LitInt = parse_macro_input!(payload);
    let suffix = n.suffix();
    if !suffix.is_empty() {
        abort_call_site!("The literal suffix `{suffix}` was unexpected.")
    }
    let digits = n.base10_digits();
    quote! {::hax_lib::int::Int::_unsafe_from_str(#digits)}.into()
}

macro_rules! make_quoting_item_proc_macro {
    ($backend:ident, $macro_name:ident, $short_name:ident, $position:expr, $cfg_name:ident) => {
        pub fn $macro_name(payload: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
            // On an inherent `impl` block, re-target the annotation onto one of its items.
            {
                let raw_payload: TokenStream = payload.clone().into();
                let attr = quote! {#[::hax_lib::$backend::$short_name(#raw_payload)]};
                if let Some(ts) = crate::quote::retarget_on_inherent_impl(&item, $position, attr) {
                    return ts.into();
                }
            }
            let mut fstar_options = None;
            let item: TokenStream = item.into();
            let payload = {
                let mut tokens = payload.into_iter().peekable();
                if let Some(pm::TokenTree::Ident(ident)) = tokens.peek() {
                    let ident_str = format!("{}", ident);
                    fstar_options = Some(ItemQuoteFStarOpts {
                        intf: ident_str == "interface" || ident_str == "both",
                        r#impl: ident_str == "impl" || ident_str == "both",
                    });
                    if !matches!(ident_str.as_str(), "impl" | "both" | "interface") {
                        abort!(ident.span(), "Expected `impl`, `both` or `interface`");
                    }
                    // Consume the ident
                    let _ = tokens.next();
                    // Expect a comma, fail otherwise
                    let comma = pm::TokenStream::from_iter(tokens.next().into_iter());
                    let _: syn::token::Comma = parse_macro_input!(comma);
                }
                pm::TokenStream::from_iter(tokens)
            };

            let ts: TokenStream = crate::quote::item(
                ItemQuote {
                    position: $position,
                    fstar_options,
                },
                quote! {#[cfg($cfg_name)]},
                payload,
                quote! {#item}.into(),
            )
            .into();
            ts.into()
        }
    };
}

macro_rules! make_quoting_proc_macro {
    ($backend:ident) => {
        pub fn ${concat($backend, _expr)}(payload: pm::TokenStream) -> pm::TokenStream {
            let ts: TokenStream = crate::quote::expression(crate::quote::InlineExprType::Unit, payload).into();
            quote!{{
                #[cfg(${concat(hax_backend_, $backend)})]
                {
                    #ts
                }
            }}.into()
        }

        pub fn ${concat($backend, _prop_expr)}(payload: pm::TokenStream) -> pm::TokenStream {
            let ts: TokenStream = crate::quote::expression(crate::quote::InlineExprType::Prop, payload).into();
            quote!{{
                #[cfg(${concat(hax_backend_, $backend)})]
                {
                    #ts
                }
                #[cfg(not(${concat(hax_backend_, $backend)}))]
                {
                    ::hax_lib::Prop::from_bool(true)
                }
            }}.into()
        }

        pub fn ${concat($backend, _unsafe_expr)}(payload: pm::TokenStream) -> pm::TokenStream {
            let ts: TokenStream = crate::quote::expression(crate::quote::InlineExprType::Anything, payload).into();
            quote!{{
                #[cfg(${concat(hax_backend_, $backend)})]
                {
                    #ts
                }
            }}.into()
        }

        make_quoting_item_proc_macro!($backend, ${concat($backend, _before)}, before, ItemQuotePosition::Before, ${concat(hax_backend_, $backend)});
        make_quoting_item_proc_macro!($backend, ${concat($backend, _after)}, after, ItemQuotePosition::After, ${concat(hax_backend_, $backend)});

        pub fn ${concat($backend, _replace)}(payload: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
            if let Ok(item_impl) = syn::parse::<ItemImpl>(item.clone()) {
                if item_impl.trait_.is_none() {
                    abort!(
                        item_impl.impl_token.span(),
                        "hax: `replace` is not supported on inherent `impl` blocks, please annotate the items of the block individually."
                    );
                }
            }
            let item: TokenStream = item.into();
            let payload: TokenStream = payload.into();
            let attr = AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
            quote! {
                #[cfg(${concat(hax_backend_, $backend)})]
                #[::hax_lib::$backend::before(#payload)]
                #attr
                #item

                #[cfg(not(${concat(hax_backend_, $backend)}))]
                #item
            }
            .into()
        }

        pub fn ${concat($backend, _replace_body)}(payload: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
            let payload: TokenStream = payload.into();
            let item: ItemFn = parse_macro_input!(item);
            let mut hax_item = item.clone();
            *hax_item.block.as_mut() = parse_quote!{
                {
                    ::hax_lib::$backend::unsafe_expr!(#payload)
                }
            };
            quote!{
                #[cfg(${concat(hax_backend_, $backend)})]
                #hax_item

                #[cfg(not(${concat(hax_backend_, $backend)}))]
                #item
            }.into()
        }
    };
    ($($backend:ident)*) => {
        $(make_quoting_proc_macro!($backend);)*
    }
}

make_quoting_proc_macro!(fstar coq proverif legacy_lean);

pub fn refinement_type(mut attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let mut item = parse_macro_input!(item as syn::ItemStruct);

    let syn::Fields::Unnamed(fields) = &item.fields else {
        abort!(
            item.generics.span(),
            "Expected a newtype (a struct with one unnamed field), got one or more named field"
        );
    };
    let paren_token = fields.paren_token;
    let fields = fields.unnamed.iter().collect::<Vec<_>>();
    let [field] = &fields[..] else {
        abort!(
            item.generics.span(),
            "Expected a newtype (a struct with one unnamed field), got {} fields",
            fields.len()
        );
    };
    if !matches!(field.vis, syn::Visibility::Inherited) {
        abort!(field.vis.span(), "This field was expected to be private");
    }

    let no_debug_assert = {
        let mut tokens = attr.clone().into_iter();
        if let (Some(pm::TokenTree::Ident(ident)), Some(pm::TokenTree::Punct(comma))) =
            (tokens.next(), tokens.next())
        {
            if ident.to_string() != "no_debug_runtime_check" {
                abort!(ident.span(), "Expected 'no_debug_runtime_check'");
            }
            if comma.as_char() != ',' {
                abort!(ident.span(), "Expected a comma");
            }
            attr = pm::TokenStream::from_iter(tokens);
            true
        } else {
            false
        }
    };

    let ExprClosure1 {
        arg: ret_binder,
        body: phi,
    } = parse_macro_input!(attr);

    let kind = FnDecorationKind::Ensures {
        ret_binder: ret_binder.clone(),
    };
    let sig = syn::Signature {
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        variadic: None,
        fn_token: syn::Token![fn](item.span()),
        ident: parse_quote! {dummy},
        generics: item.generics.clone(),
        paren_token,
        inputs: syn::punctuated::Punctuated::new(),
        output: syn::ReturnType::Type(parse_quote! {->}, Box::new(field.ty.clone())),
    };
    let ident = &item.ident;
    let generics = &item.generics;
    let vis = item.vis.clone();
    let generics_args: syn::punctuated::Punctuated<_, syn::token::Comma> = item
        .generics
        .params
        .iter()
        .map(|g| match g {
            syn::GenericParam::Lifetime(p) => {
                let i = &p.lifetime;
                quote! { #i }
            }
            syn::GenericParam::Type(p) => {
                let i = &p.ident;
                quote! { #i }
            }
            syn::GenericParam::Const(p) => {
                let i = &p.ident;
                quote! { #i }
            }
        })
        .collect();
    let inner_ty = &field.ty;
    let (refinement_item, refinement_attr) =
        make_fn_decoration(phi.clone(), sig, kind, None, None, SelfProjection::Unknown);
    let module_ident = syn::Ident::new(
        &format!("hax__autogenerated_refinement__{}", ident),
        ident.span(),
    );

    item.vis = parse_quote! {pub};
    let debug_assert =
        no_debug_assert.then_some(quote! {::core::debug_assert!(Self::invariant(x.clone()));});
    let newtype_as_ref_attr = AttrPayload::NewtypeAsRefinement;
    quote! {
        #[allow(non_snake_case)]
        mod #module_ident {
            #[allow(unused_imports)]
            use super::*;

            #refinement_item

            #newtype_as_ref_attr
            #refinement_attr
            #item

            #[::hax_lib::exclude]
            impl #generics ::hax_lib::Refinement for #ident <#generics_args> {

                type InnerType = #inner_ty;

                fn new(x: Self::InnerType) -> Self {
                    #debug_assert
                    Self(x)
                }
                fn get(self) -> Self::InnerType {
                    self.0
                }
                fn get_mut(&mut self) -> &mut Self::InnerType {
                    &mut self.0
                }
                fn invariant(#ret_binder: Self::InnerType) -> ::hax_lib::Prop {
                    ::hax_lib::Prop::from(#phi)
                }
            }

            #[::hax_lib::exclude]
            impl #generics ::core::ops::Deref for #ident <#generics_args> {
                type Target = #inner_ty;
                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            #[::hax_lib::exclude]
            impl #generics ::hax_lib::RefineAs<#ident <#generics_args>> for #inner_ty {
                fn into_checked(self) -> #ident <#generics_args> {
                    use ::hax_lib::Refinement;
                    #ident::new(self)
                }
            }
        }
        #vis use #module_ident::#ident;

    }
    .into()
}
