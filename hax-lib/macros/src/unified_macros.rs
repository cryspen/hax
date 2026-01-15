pub mod evaluate;
mod item_container;
use std::{collections::HashMap, ops::Add};

// pub use item_container::ItemContainer;

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::ToTokens;
use syn::{
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    token::{Brace, Comma},
    visit::Visit,
    *,
};

use crate::merge_generics;

struct ApplyMacrosWithEnvironment {
    function_macros: HashMap<String, fn(HaxMacroInput) -> TokenStream>,
    derive_macros: HashMap<String, fn(HaxMacroInput) -> TokenStream>,
    attribute_macros: HashMap<String, fn(HaxMacroInput, TokenStream) -> TokenStream>,
    env: Env,
}

// declare_proc_macro! {
//     #[proc_macro_attribute]
//     pub fn heyho(attr : TokenStream, input: HaxMacroInput) -> HaxMacroOutput {
//         todo!()
//     }
// }

#[derive(Default)]
pub struct GenericContext {
    pub lg_token: Token![<],
    pub generics: Punctuated<syn::GenericParam, Comma>,
    pub gt_token: Token![>],
    pub where_token: Token![where],
    pub predicates: Punctuated<WherePredicate, Comma>,
}

impl Parse for GenericContext {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            lg_token: input.parse()?,
            generics: Punctuated::parse_terminated(input)?,
            gt_token: input.parse()?,
            where_token: input.parse()?,
            predicates: Punctuated::parse_terminated(input)?,
        })
    }
}

/// A (generic) environment.
#[derive(Default, Clone, Debug)]
pub struct Env {
    pub self_type: Option<syn::Type>,
    pub generics: syn::Generics,
}

mod kw {
    use syn::custom_keyword;
    custom_keyword!(hax_macro_generic_env);
}

#[derive(Clone, Default)]
pub struct EnvPayload {
    pub at1: Token![@],
    pub at2: Token![@],
    pub env_kw: kw::hax_macro_generic_env,
    pub brace1: Brace,
    pub self_type: Option<syn::Type>,
    pub brace2: Brace,
    pub generics: syn::Generics,
}

impl From<Env> for EnvPayload {
    fn from(value: Env) -> Self {
        Self {
            at1: Default::default(),
            at2: Default::default(),
            env_kw: Default::default(),
            brace1: Default::default(),
            self_type: value.self_type,
            brace2: Default::default(),
            generics: value.generics,
        }
    }
}

impl EnvPayload {
    pub fn env(&self) -> Env {
        Env {
            self_type: self.self_type.clone(),
            generics: self.generics.clone(),
        }
    }
}

pub struct WithEnvPayload<T> {
    pub env_payload: Option<EnvPayload>,
    pub value: T,
}

impl<T: Parse> Parse for WithEnvPayload<T> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            env_payload: input.parse().ok(),
            value: input.parse()?,
        })
    }
}

impl Parse for EnvPayload {
    fn parse(input: ParseStream) -> Result<Self> {
        let (self_type, generics);
        Ok(Self {
            at1: input.parse()?,
            at2: input.parse()?,
            env_kw: input.parse()?,
            brace1: braced!(self_type in input),
            self_type: if self_type.is_empty() {
                None
            } else {
                Some(self_type.parse()?)
            },
            brace2: braced!(generics in input),
            generics: generics.parse()?,
        })
    }
}

impl ToTokens for EnvPayload {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        self.at1.to_tokens(tokens);
        self.at2.to_tokens(tokens);
        self.env_kw.to_tokens(tokens);
        self.brace1.surround(tokens, |tokens| {
            if let Some(ty) = &self.self_type {
                ty.to_tokens(tokens);
            }
        });
        self.brace2.surround(tokens, |tokens| {
            self.generics.to_tokens(tokens);
        });
    }
}

impl<T: ToTokens> ToTokens for WithEnvPayload<T> {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        if let Some(env_payload) = &self.env_payload {
            env_payload.to_tokens(tokens);
        }
        self.value.to_tokens(tokens);
    }
}

impl Env {
    /// Build an `Env` from any `syn::Item`.
    ///
    /// - `impl`: `self_type = Some(<SelfTy>)`, `generics = impl.generics.clone()`
    /// - `trait`: `self_type = None`, `generics` cloned and augmented with `where Self: <supertraits>`
    /// - others with generics (struct/enum/union/type/trait alias): `self_type = None`, plain generics
    /// - items without generics: `None`
    pub fn from_item(item: &Item) -> Option<Self> {
        match item {
            Item::Impl(i) => Some(Self::from_impl(i)),
            Item::Trait(tr) => Some(Self::from_trait(tr)),
            Item::TraitAlias(a) => Some(Self {
                self_type: None,
                generics: a.generics.clone(),
            }),
            Item::Struct(s) => Some(Self {
                self_type: None,
                generics: s.generics.clone(),
            }),
            Item::Enum(e) => Some(Self {
                self_type: None,
                generics: e.generics.clone(),
            }),
            Item::Union(u) => Some(Self {
                self_type: None,
                generics: u.generics.clone(),
            }),
            Item::Type(t) => Some(Self {
                self_type: None,
                generics: t.generics.clone(),
            }),
            // No generics/`Self` context to speak of:
            Item::Fn(_)
            | Item::Const(_)
            | Item::Static(_)
            | Item::Mod(_)
            | Item::ForeignMod(_)
            | Item::Use(_)
            | Item::Macro(_)
            | Item::Verbatim(_)
            | Item::ExternCrate(_) => None,
            // Forward-compat fallback:
            _ => None,
        }
    }

    fn from_impl(i: &ItemImpl) -> Self {
        Env {
            self_type: Some((*i.self_ty).clone()),
            generics: i.generics.clone(),
        }
    }

    fn from_trait(tr: &ItemTrait) -> Self {
        let mut generics: Generics = tr.generics.clone();
        let self_typ: Type = parse_quote!(Self);

        // Collect supertraits (e.g., `Send + Display + 'static`)
        let bounds: Punctuated<TypeParamBound, Token![+]> = tr.supertraits.clone();

        if !bounds.is_empty() {
            // Ensure a where-clause exists, then push `Self: <bounds>`
            let wc = generics.make_where_clause();
            let pred: WherePredicate = WherePredicate::Type(PredicateType {
                lifetimes: None,
                bounded_ty: self_typ.clone(),
                colon_token: <Token![:]>::default(),
                bounds,
            });
            wc.predicates.push(pred);
        }

        let mut self_generics = Generics::default();
        self_generics
            .params
            .push(GenericParam::Type(TypeParam::from(Ident::new(
                "Self",
                Span::call_site(),
            ))));
        generics = merge_generics(self_generics, generics.clone());

        Env {
            self_type: None,
            generics,
        }
    }
}

impl Add<Env> for Env {
    type Output = Self;
    fn add(
        mut self,
        Self {
            self_type,
            generics,
        }: Self,
    ) -> Self::Output {
        if self.self_type.is_none() {
            self.self_type = self_type;
        }
        self + generics
    }
}
impl Add<Generics> for Env {
    type Output = Self;
    fn add(mut self, generics: Generics) -> Self::Output {
        self.generics = merge_generics(std::mem::take(&mut self.generics), generics);
        self
    }
}

#[derive(Default)]
pub struct HaxMacroInput {
    pub parent_generics: Option<Env>,
    pub token_stream: TokenStream,
}

// impl Parse for Env {
//     fn parse(input: ParseStream) -> Result<Self> {
//         let (self_type, generics);
//         Ok(Self {
//             brace_token: braced!(self_type in input),
//             self_type: if self_type.is_empty() {
//                 None
//             } else {
//                 Some(self_type.parse()?)
//             },
//             brace_token2: braced!(generics in input),
//             generics: generics.parse()?,
//         })
//     }
// }

// impl Parse for HaxMacroInput {
//     fn parse(input: ParseStream) -> Result<Self> {
//         let content;
//         Ok(Self {
//             brace_token: braced!(content in input),
//             generics: content.parse()?,
//             token_stream: TokenStream2::into(input.parse()?),
//         })
//     }
// }

pub struct HaxMacroOutput {
    pub token_stream: TokenStream2,
    pub extra_items: Vec<TokenStream2>,
}

impl HaxMacroOutput {
    fn into_token_stream(self) -> TokenStream {
        todo!()
        // let Self {
        //     token_stream,
        //     extra_items,
        // } = self;
        // if !extra_items.is_empty() {
        //     let token_stream: proc_macro::TokenStream = token_stream.into();
        //     let mut input = ::syn::parse_macro_input!(token_stream as ItemContainer);
        //     input.insert_item(::quote::quote! {#(#extra_items)*});
        //     use quote::ToTokens;
        //     input.into_token_stream()
        // } else {
        //     token_stream
        // }
        // .into()
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct HasSelf {
    self_detected: bool,
    root_item: bool,
}

impl<'ast> Visit<'ast> for HasSelf {
    fn visit_item(&mut self, i: &'ast syn::Item) {
        if !self.root_item {
            return;
        }
        self.root_item = false;
        visit::visit_item(self, i);
    }

    fn visit_type_path(&mut self, i: &'ast syn::TypePath) {
        self.self_detected |= i.path.segments.iter().any(|seg| seg.ident == "Self");
        visit::visit_type_path(self, i);
    }

    fn visit_expr_path(&mut self, i: &'ast syn::ExprPath) {
        self.self_detected |= i.path.is_ident("self");
        visit::visit_expr_path(self, i);
    }

    fn visit_receiver(&mut self, _i: &'ast syn::Receiver) {
        self.self_detected = true;
    }

    fn visit_pat_ident(&mut self, i: &'ast syn::PatIdent) {
        self.self_detected |= i.ident == "self";
        visit::visit_pat_ident(self, i);
    }
}
