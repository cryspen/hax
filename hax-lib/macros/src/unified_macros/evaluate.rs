use crate::{simple_path_idents, unified_macros::WithEnvPayload};

use super::{Env, HaxMacroInput};
use proc_macro2::TokenStream;
use quote::ToTokens;
use std::collections::HashMap;
use syn::{
    visit_mut::{self, VisitMut},
    ItemImpl, Meta,
};

use crate::utils::{impl_item_attrs_mut, impl_item_generics_mut, item_attrs_mut, RetainMapExt};

pub struct ApplyMacrosWithEnvironment {
    recognized_prefixes: Vec<Vec<String>>,
    parent_generics: Option<Env>,
}

impl ApplyMacrosWithEnvironment {
    fn is_recongized_macro(&self, path: &syn::Path) -> bool {
        let path = simple_path_idents(&path).unwrap_or_default();
        let path = path.iter().map(String::as_str).collect::<Vec<_>>();
        let name = match path.as_slice() {
            &["hax_lib", name] => name,
            &[name] => name,
            _ => return false,
        };
        name == "requires"
    }

    fn try_rewrite_any_macro(&self, path: &syn::Path, tokens: &mut TokenStream) {
        let Some(parent_generics) = &self.parent_generics else {
            return;
        };
        if self.is_recongized_macro(path) {
            let value = std::mem::take(tokens);
            *tokens = WithEnvPayload {
                env_payload: Some(parent_generics.clone().into()),
                value,
            }
            .into_token_stream();
        }
    }

    fn with_env(&mut self, env: Env, mut f: impl FnMut(&mut Self)) {
        let previous = self.parent_generics.clone();
        self.parent_generics = Some(env);

        f(self);

        self.parent_generics = previous;
    }

    fn try_rewrite_attribute_macro<'a>(
        &self,
        attributes: impl Iterator<Item = &'a mut syn::Attribute>,
    ) {
        for attr in attributes {
            let Meta::List(meta_list) = &mut attr.meta else {
                continue;
            };
            self.try_rewrite_any_macro(&meta_list.path, &mut meta_list.tokens);
        }
    }
}

impl VisitMut for ApplyMacrosWithEnvironment {
    fn visit_impl_item_mut(&mut self, i: &mut syn::ImplItem) {
        if let Some(generics) = impl_item_generics_mut(i) {
            let Some(parent_generics) = &self.parent_generics else {
                // *i = syn::ImplItem::Verbatim();
                return;
            };
            self.with_env(parent_generics.clone() + generics.clone(), |visitor| {
                visitor.try_rewrite_attribute_macro(impl_item_attrs_mut(i).into_iter().flatten());
                visit_mut::visit_impl_item_mut(visitor, i)
            });
        }
    }
    fn visit_item_mut(&mut self, i: &mut syn::Item) {
        self.try_rewrite_attribute_macro(item_attrs_mut(i).into_iter().flatten());

        if let Some(env) = Env::from_item(i) {
            self.with_env(env, |visitor| visit_mut::visit_item_mut(visitor, i));
        }

        visit_mut::visit_item_mut(self, i);
    }
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Macro(syn::ExprMacro { mac, .. }) = expr {
            self.try_rewrite_any_macro(&mac.path, &mut mac.tokens);
        };

        visit_mut::visit_expr_mut(self, expr);
    }
}
