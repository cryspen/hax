extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Group, TokenStream as TokenStream2, TokenTree};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::{Ident, Token, parse_macro_input};

mod kw {
    syn::custom_keyword!(include);
}

fn replace_in_stream(
    stream: TokenStream2,
    target: &Ident,
    replacement: &TokenStream2,
) -> TokenStream2 {
    stream
        .into_iter()
        .flat_map(|tt| match tt {
            TokenTree::Ident(ident) if ident == *target => {
                replacement.clone().into_iter().collect()
            }
            TokenTree::Group(group) => {
                let new_stream = replace_in_stream(group.stream(), target, replacement);
                let mut new_group = Group::new(group.delimiter(), new_stream);
                new_group.set_span(group.span());
                vec![TokenTree::Group(new_group)]
            }
            other => vec![other],
        })
        .collect()
}

// The arguments that the `replace` proc-macro can take
struct AttributeArgs {
    target: Ident,
    replacement: TokenStream2,
}

impl Parse for AttributeArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let target: Ident = input.parse()?;
        input.parse::<Token![=>]>()?;
        let include_clause = |input: ParseStream| -> Result<Ident> {
            input.parse::<kw::include>()?;
            let content;
            syn::parenthesized!(content in input);
            content.parse()
        }(input)
        .ok();
        Ok(AttributeArgs {
            target,
            replacement: match include_clause {
                Some(clause) => match clause.to_string().as_str() {
                    "VisitableAstNodes" => quote! {
                        Expr, Pat, ExprKind, PatKind, Ty, TyKind, Metadata, Literal,
                        LocalId, Lhs, Symbol, LoopKind, SafetyKind, Quote,
                        SpannedTy, BindingMode, PrimitiveTy, Region, ImplExpr,
                        IntKind, FloatKind, GenericValue, Arm, LoopState, ControlFlowKind,
                        DynTraitGoal, Attribute, QuoteContent, BorrowKind,
                        TraitGoal, ImplExprKind, IntSize, Signedness, Guard, AttributeKind,
                        GuardKind, ImplItem, ImplItemKind, TraitItem, TraitItemKind,
                        ItemQuoteOrigin, ItemQuoteOriginKind, ItemQuoteOriginPosition, GenericParamKind, ImplIdent,
                        ProjectionPredicate, GenericParam, Generics, DocCommentKind, Param, Variant, ItemKind, Item,
                        GenericConstraint, ErrorNode, Module,

                        ResugaredExprKind, ResugaredTyKind, ResugaredPatKind,
                        ResugaredImplItemKind, ResugaredTraitItemKind, ResugaredItemKind
                    }.into(),
                    _ => {
                        return Err(syn::Error::new_spanned(
                            clause,
                            format!("This is not a recognized include pragma."),
                        ));
                    }
                },
                None => input.parse::<TokenStream2>()?,
            },
        })
    }
}

pub fn replace(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as AttributeArgs);
    let item_stream: TokenStream2 = item.into();
    replace_in_stream(item_stream, &args.target, &args.replacement).into()
}
