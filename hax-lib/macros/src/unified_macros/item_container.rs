use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use syn::{
    Expr, ImplItemConst, ImplItemFn, Item, ItemMod, ItemStatic, TraitItemConst, TraitItemFn,
    parse::{Parse, ParseStream},
    parse_quote,
    visit::{self, Visit},
};

/// A Rust item that can contain other items within its body or block.
///
/// This enum represents high-level Rust constructs (like functions, modules, or impl items)
/// that can serve as containers for nested items or declarations. These variants wrap specific
/// `syn` item types that support inner items or statements in their bodies.
///
/// Variants:
/// - `Const`: A constant item within an `impl` block (`ImplItemConst`)
/// - `Fn`: A function item within an `impl` block (`ImplItemFn`)
/// - `Mod`: A module item (`ItemMod`) that can contain other items directly
/// - `Static`: A static item (`ItemStatic`) that may support a block-like expression
pub enum ItemContainer {
    Const(syn::ImplItemConst),
    Fn(syn::ImplItemFn),
    Mod(syn::ItemMod),
    Static(syn::ItemStatic),
}

impl ToTokens for ItemContainer {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            ItemContainer::Const(inner) => inner.to_tokens(tokens),
            ItemContainer::Fn(inner) => inner.to_tokens(tokens),
            ItemContainer::Mod(inner) => inner.to_tokens(tokens),
            ItemContainer::Static(inner) => inner.to_tokens(tokens),
        }
    }
}

impl ItemContainer {
    /// Insert an item inside an `ItemContainer`.
    pub fn insert_item(&mut self, extra_items: TokenStream2) {
        let replace_expr = |expr: &mut Expr, extra_items: TokenStream2| {
            let mut original_expr: Expr = Expr::Verbatim(TokenStream2::new());
            std::mem::swap(expr, &mut original_expr);
            *expr = parse_quote! {{
                #extra_items
                #original_expr
            }};
        };
        match self {
            ItemContainer::Const(ImplItemConst { expr, .. }) => replace_expr(expr, extra_items),
            ItemContainer::Fn(ImplItemFn { block, .. }) => {
                block
                    .stmts
                    .insert(0, syn::Stmt::Item(Item::Verbatim(extra_items)));
            }
            ItemContainer::Mod(ItemMod { content, .. }) => match content {
                Some((_, content)) => content.insert(0, Item::Verbatim(extra_items.clone().into())),
                None => unreachable!("non-inline `mod` are rejected by `<NestableItem as Parse>`"),
            },
            ItemContainer::Static(ItemStatic { expr, .. }) => {
                replace_expr(expr.as_mut(), extra_items)
            }
        }
    }
}

impl Parse for ItemContainer {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if let Ok(value) = input.parse() {
            Ok(Self::Const(value))
        } else if let Ok(value) = input.parse() {
            Ok(Self::Fn(value))
        } else if let Ok(value) = input.parse::<ItemMod>() {
            if value.content.is_none() {
                return Err(syn::Error::new(
                    input.span(),
                    "Non-inline module (e.g. `mod my_module;`)",
                ));
            };
            Ok(Self::Mod(value))
        } else if let Ok(value) = input.parse() {
            Ok(Self::Static(value))
        } else if let Ok(_) = input.parse::<TraitItemFn>() {
            Err(syn::Error::new(
                input.span(),
                "Trait method with no default implementation.",
            ))
        } else if let Ok(_) = input.parse::<TraitItemConst>() {
            Err(syn::Error::new(
                input.span(),
                "Trait const with no default implementation.",
            ))
        } else {
            Err(syn::Error::new(
                input.span(),
                "Expected an inline module, a static, or (possibly associated) function or constant.",
            ))
        }
    }
}
