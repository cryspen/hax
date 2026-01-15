use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use syn::{
    Block, Expr, ExprBlock, ExprTuple, ImplItem, ImplItemConst, ImplItemFn, ImplItemType, Item,
    ItemConst, ItemFn, ItemMod, ItemStatic, ItemType, Stmt, TraitItem, TraitItemConst, TraitItemFn,
    TraitItemType,
    parse::{Parse, ParseStream},
    parse_quote,
    token::Brace,
    visit::{self, Visit},
};

/// Items in which expressions can be injected.
/// Only the items that may be under a trait or impl block are represented.
/// In any other case, injecting an expression can be done by prepending the item with a `const _: () = {};` block.
enum InjectableItems {
    ImplItemFn(ImplItemFn),
    TraitItemFn(TraitItemFn),

    ImplItemType(ImplItemType),
    TraitItemType(TraitItemType),

    ItemConst(ImplItemConst),
    TraitItemConst(TraitItemConst),
}

impl ToTokens for InjectableItems {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            InjectableItems::ImplItemFn(impl_item_fn) => impl_item_fn.to_tokens(tokens),
            InjectableItems::TraitItemFn(trait_item_fn) => trait_item_fn.to_tokens(tokens),
            InjectableItems::ImplItemType(impl_item_type) => impl_item_type.to_tokens(tokens),
            InjectableItems::TraitItemType(trait_item_type) => trait_item_type.to_tokens(tokens),
            InjectableItems::ItemConst(impl_item_const) => impl_item_const.to_tokens(tokens),
            InjectableItems::TraitItemConst(trait_item_const) => trait_item_const.to_tokens(tokens),
        }
    }
}

impl Parse for InjectableItems {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        macro_rules! parse {
            ($($variant:ident),*) => {
                $(if let Ok(value) = input.parse() {
                    return Ok(Self::$variant(value));
                })*
            };
        }

        parse!(ImplItemFn, TraitItemFn);
        parse!(ImplItemType, TraitItemType);
        parse!(ItemConst, TraitItemConst);

        Err(syn::Error::new(
            input.span(),
            "Could not parse as an InjectableItems.",
        ))
    }
}

/// Add extra item inside or near a base item.
/// The items will be added somewhere in a way that will work normally within trait or impl blocks (e.g. not adding extra items superficially).
/// Also, the added items will be placed in a anonymous const block.
pub fn insert_anonymous_items(base_item: TokenStream2, extra_items: TokenStream2) -> TokenStream2 {
    let extra_item: Item = parse_quote! {const _: () = { #extra_items };};
    match syn::parse2::<InjectableItems>(base_item.clone()) {
        Ok(mut injectable_items) => {
            injectable_items.insert(extra_item);
            injectable_items.into_token_stream()
        }
        _ => {
            quote::quote! {#extra_item #base_item}
        }
    }
}

impl InjectableItems {
    fn insert(&mut self, item: Item) {
        self.with_block(move |block: &mut Block| {
            block.stmts.insert(0, Stmt::Item(item));
        });
    }

    fn with_block(&mut self, f: impl FnOnce(&mut Block)) {
        fn with_block_in_type(ty: &mut syn::Type, f: impl FnOnce(&mut Block)) {
            let mut block: Block = parse_quote!({ true });
            f(&mut block);
            *ty = parse_quote!(::hax_lib::HaxDummyType<#block, #ty>);
        }
        fn with_block_in_expr(expr: &mut syn::Expr, f: impl FnOnce(&mut Block)) {
            let inner = std::mem::replace(expr, Expr::Verbatim(TokenStream2::new()));
            let mut block = Block {
                brace_token: Brace::default(),
                stmts: vec![Stmt::Expr(inner, None)],
            };
            f(&mut block);
            *expr = Expr::Block(ExprBlock {
                attrs: vec![],
                label: None,
                block,
            });
        }

        match self {
            InjectableItems::ImplItemFn(impl_item_fn) => f(&mut impl_item_fn.block),
            InjectableItems::TraitItemFn(trait_item_fn) => {
                if let Some(block) = &mut trait_item_fn.default {
                    f(block);
                } else {
                    let mut ty = match trait_item_fn.sig.output.clone() {
                        syn::ReturnType::Default => parse_quote!(()),
                        syn::ReturnType::Type(_, ty) => (&*ty).clone(),
                    };
                    with_block_in_type(&mut ty, f);
                    trait_item_fn.sig.output = parse_quote!(-> #ty);
                }
            }
            InjectableItems::ImplItemType(impl_item_type) => {
                with_block_in_type(&mut impl_item_type.ty, f);
            }
            InjectableItems::TraitItemType(trait_item_type) => {
                let mut block: Block = parse_quote!({ true });
                f(&mut block);
                trait_item_type
                    .bounds
                    .push(parse_quote!(::hax_lib::HaxDummyTrait<#block>));
            }
            InjectableItems::ItemConst(item_const) => {
                with_block_in_expr(&mut item_const.expr, f);
            }
            InjectableItems::TraitItemConst(trait_item_const) => {
                if let Some((_, body)) = &mut trait_item_const.default {
                    with_block_in_expr(body, f);
                } else {
                    with_block_in_type(&mut trait_item_const.ty, f);
                }
            }
        }
    }
}
