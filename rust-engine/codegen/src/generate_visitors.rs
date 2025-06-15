use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse_quote, visit::Visit, visit_mut::VisitMut, Attribute, Fields, File, Ident, ItemEnum,
    ItemStruct, Meta, PathArguments,
};

/// Just the AST node, without payload.
#[derive(Debug, Clone)]
pub enum VisitableItemKind {
    Struct(ItemStruct),
    Enum(ItemEnum),
}

#[derive(Debug, Clone)]
pub enum VisitableOptions {
    Opaque,
    ManualDerive(Vec<String>),
}

#[derive(Debug, Clone)]
struct VisitableItem {
    pub mod_path: syn::Path,
    pub options: Option<VisitableOptions>,
    pub ident: Ident,
    pub generics: syn::Generics,
    pub kind: VisitableItemKind,
}

/// Walks a `syn::File` and collects every `(VisitableKind, payload)`.
struct VisitableCollector {
    current_module: syn::Path,
    items: Vec<VisitableItem>,
}

impl Default for VisitableCollector {
    fn default() -> Self {
        Self {
            current_module: parse_quote!(crate),
            items: Default::default(),
        }
    }
}

impl VisitableCollector {
    fn insert(
        &mut self,
        kind: VisitableItemKind,
        attr_payload: TokenStream,
        ident: Ident,
        generics: syn::Generics,
    ) {
        let attr_payload: String = attr_payload
            .to_string()
            .chars()
            .filter(|c| *c != ' ')
            .collect();
        let options = if attr_payload == "opaque" {
            Some(VisitableOptions::Opaque)
        } else {
            (|| {
                Some(VisitableOptions::ManualDerive(
                    attr_payload
                        .strip_prefix("manual_driver")?
                        .strip_suffix(")")?
                        .split(",")
                        .map(str::to_string)
                        .collect(),
                ))
            })()
        };
        self.items.push(VisitableItem {
            mod_path: self.current_module.clone(),
            options,
            ident,
            generics,
            kind,
        });
    }
}

impl<'a> Visit<'a> for VisitableCollector {
    fn visit_item_mod(&mut self, i: &'a syn::ItemMod) {
        let prev_module = self.current_module.clone();
        let i_ident = &i.ident;
        self.current_module = parse_quote!(#prev_module :: #i_ident);
        syn::visit::visit_item_mod(self, i);
        self.current_module = prev_module.clone();
    }
    fn visit_item_struct(&mut self, node: &ItemStruct) {
        if let Some(payload) = extract_visitable_payload(&node.attrs) {
            self.insert(
                VisitableItemKind::Struct(node.clone()),
                payload,
                node.ident.clone(),
                node.generics.clone(),
            );
        }
        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &ItemEnum) {
        if let Some(payload) = extract_visitable_payload(&node.attrs) {
            self.insert(
                VisitableItemKind::Enum(node.clone()),
                payload,
                node.ident.clone(),
                node.generics.clone(),
            );
        }
        syn::visit::visit_item_enum(self, node);
    }
}

fn extract_visitable_payload(attrs: &[Attribute]) -> Option<TokenStream> {
    // eprintln!("{:#?}", attrs);
    attrs.iter().find_map(|attr| match &attr.meta {
        Meta::List(m) if m.path.is_ident("visitable") => Some(m.tokens.clone()),
        Meta::Path(path) if path.is_ident("visitable") => Some(quote! {}),
        _ => None,
    })
}

fn get_hax_sources() -> File {
    let mut module = super::read("src/lib.rs");
    let mut inliner = super::visitors::inline_mods::ModuleInliner::new("src");
    inliner.visit_file_mut(&mut module);
    module
}

#[derive(Copy, Clone, Debug)]
struct VisitorKind {
    /// Can this visitor short circuit control flow?
    pub short_circuiting: bool,
    /// When visiting a type (say `Expr`), do we take a `&mut Expr` (then `map` is true) or a `&'a Expr`?
    pub map: bool,
    /// Visitor returns some value (the type must be a monoid)
    pub reduce: bool,
}

struct VisitorBuilder<'a> {
    pub kind: VisitorKind,
    /// Types allowed to be visited
    pub types: &'a Vec<VisitableItem>,
}

enum Ty {
    Vec(Box<Ty>),
    Box(Box<Ty>),
    Tuple(Vec<Ty>),
    Ident(Ident),
}

impl Ty {
    fn interpret(ty: syn::Type, allowed: &impl Fn(&Ident) -> bool) -> Option<Self> {
        if let syn::Type::Tuple(tuple) = ty {
            return Some(Ty::Tuple(
                tuple
                    .elems
                    .into_iter()
                    .map(|t| Ty::interpret(t, allowed))
                    .collect::<Option<Vec<_>>>()?,
            ));
        }
        let syn::Type::Path(type_path) = ty else {
            unimplemented!()
            // return None;
        };
        let Some(last) = type_path.path.segments.iter().last() else {
            unimplemented!()
            // return None
        };
        let type_args = match &last.arguments {
            PathArguments::AngleBracketed(args) => args
                .args
                .iter()
                .cloned()
                .flat_map(|x| match x {
                    syn::GenericArgument::Type(t) => Some(t),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        };
        match (last.ident.to_string().as_str(), &type_args[..]) {
            ("Vec", [t]) => return Some(Ty::Vec(Box::new(Ty::interpret(t.clone(), allowed)?))),
            ("Box", [t]) => return Some(Ty::Box(Box::new(Ty::interpret(t.clone(), allowed)?))),
            _ => (),
        };
        allowed(&last.ident).then_some(Self::Ident(last.ident.clone()))
    }
}

use crate::visitors::utils::{field_idents, field_typed_idents, fields_to_payload};

impl VisitorKind {
    fn name_components(&self) -> Vec<&str> {
        vec![
            Some("visitor"),
            self.map.then_some("map"),
            self.reduce.then_some("reduce"),
            self.short_circuiting.then_some("cf"),
        ]
        .into_iter()
        .flatten()
        .collect()
    }
    fn kind(&self) -> String {
        self.name_components()[1..].join("_")
    }
    fn module_name(&self) -> Ident {
        let name = self.name_components().join("_");
        Ident::new(&name, Span::call_site())
    }
    fn trait_name(&self) -> Ident {
        fn capitalize_first(s: &str) -> String {
            let mut chars = s.chars();
            match chars.next() {
                None => String::new(),
                Some(first) => {
                    let first_up = first.to_uppercase().collect::<String>();
                    format!("{}{}", first_up, chars.as_str())
                }
            }
        }

        let name = self
            .name_components()
            .into_iter()
            .map(capitalize_first)
            .collect::<Vec<_>>()
            .join("");
        Ident::new(&name, Span::call_site())
    }
}

impl<'a> VisitorBuilder<'a> {
    fn visitable_ty(&self, ty: &Ident) -> bool {
        self.types.iter().any(|item| &item.ident == ty)
    }
    fn visit_function_name(&self, ty: &Ident) -> Ident {
        fn to_snake_case(s: &str) -> String {
            s.chars().fold(String::new(), |mut acc, c| {
                if c.is_uppercase() && !acc.is_empty() {
                    acc.push('_');
                }
                acc.extend(c.to_lowercase());
                acc
            })
        }
        let ty = to_snake_case(&ty.to_string());
        Ident::new(&format!("visit_{ty}"), Span::call_site())
    }
    fn visit_function_name_manual(&self, ty: &Ident) -> Ident {
        let fun_name = self.visit_function_name(ty).to_string();
        let mod_name = self.kind.module_name();
        Ident::new(&format!("manual_{mod_name}_{fun_name}"), Span::call_site())
    }
    fn generate_module(&self, manual_drivers: &mut Vec<TokenStream>) -> TokenStream {
        let types = self.types.as_slice();
        let trait_definition = self.generate_trait(types);
        let driver_functions = self.generate_driver_functions(types, manual_drivers);
        let module_name = self.kind.module_name();
        quote! {
            mod #module_name {
                use super::*;
                #trait_definition
                #driver_functions
            }
        }
    }
    fn generate_driver_functions(
        &self,
        items: &[VisitableItem],
        manual_drivers: &mut Vec<TokenStream>,
    ) -> TokenStream {
        let methods: Vec<_> = items
            .iter()
            .map(|item| self.generate_driver_function(item, manual_drivers))
            .collect();
        quote! {#(#methods)*}
    }
    fn generate_method(&self, item: &VisitableItem) -> TokenStream {
        let type_ident = &item.ident;
        let method = self.visit_function_name(type_ident);
        let sig = self.signature(item, true, false);
        quote! {
            #sig {
                #method(self, v)
            }
        }
    }
    fn trait_generics(&self) -> TokenStream {
        if self.kind.map {
            quote! {}
        } else {
            quote! {'lt}
        }
    }
    fn borrow(&self) -> TokenStream {
        if self.kind.map {
            quote! {&mut}
        } else {
            quote! {&'lt}
        }
    }
    fn parent_bounds(&self) -> Option<TokenStream> {
        self.kind.reduce.then_some(quote! {+ Monoid})
    }
    fn generate_trait(&self, items: &[VisitableItem]) -> TokenStream {
        let trait_name = self.kind.trait_name();
        let generics = self.trait_generics();
        let methods: Vec<_> = items
            .iter()
            .map(|item| self.generate_method(item))
            .collect();
        let parent_bounds = self.parent_bounds();
        let assoc_types = self.kind.short_circuiting.then_some(quote! {type Error;});
        quote! {
            pub trait #trait_name<#generics>: Sized #parent_bounds {
                #assoc_types
                #(#methods)*
            }
        }
    }
    fn signature(&self, item: &VisitableItem, from_method: bool, manual: bool) -> TokenStream {
        let method = if manual {
            self.visit_function_name_manual(&item.ident)
        } else {
            self.visit_function_name(&item.ident)
        };
        let borrow = self.borrow();
        let self_ty = &item.ident;
        let ret = self.return_type(from_method);
        if from_method {
            quote! {fn #method(&mut self, v: #borrow #self_ty) -> #ret}
        } else {
            let trait_name = self.kind.trait_name();
            let parent_bounds = self.parent_bounds();
            let mut trait_generics = self.trait_generics();
            if !trait_generics.is_empty() {
                trait_generics = quote! {#trait_generics,};
            }
            quote! {pub fn #method<#trait_generics V: #trait_name<#trait_generics> #parent_bounds>(visitor: &mut V, v: #borrow #self_ty) -> #ret}
        }
    }
    fn generate_driver_function(
        &self,
        item: &VisitableItem,
        manual_drivers: &mut Vec<TokenStream>,
    ) -> TokenStream {
        let type_ident = &item.ident;
        let sig = self.signature(item, false, false);
        match &item.options {
            Some(VisitableOptions::ManualDerive(target))
                if target.len() == 0 || target.contains(&self.kind.kind()) =>
            {
                let manual_driver = self.visit_function_name_manual(&item.ident);
                let sig_manual_driver = self.signature(item, false, true);
                manual_drivers.push(quote! {#sig_manual_driver {todo!()}});
                return quote! {
                    #sig {
                        #manual_driver(visitor, v)
                    }
                };
            }
            Some(VisitableOptions::Opaque) => {
                let v = self.default_value();
                return quote! {
                   #[allow(unused)]  #sig {
                        let _ = v;
                        #v
                    }
                };
            }
            _ => (),
        }

        let variants = match &item.kind {
            VisitableItemKind::Struct(item_struct) => {
                vec![(quote!(#type_ident), &item_struct.fields)]
            }
            VisitableItemKind::Enum(item_enum) => item_enum
                .variants
                .iter()
                .map(|variant| {
                    let ident = &variant.ident;
                    (quote!(#type_ident::#ident), &variant.fields)
                })
                .collect(),
        };
        let arms = variants
            .into_iter()
            .map(|(ident, fields)| self.generate_arm(ident, fields))
            .collect::<Vec<_>>();
        quote! {
            #[allow(unused)] #sig {
                match v {
                    #(#arms)*
                }
            }
        }
    }
    fn return_type(&self, from_method: bool) -> TokenStream {
        let visitor = if from_method {
            quote! {Self}
        } else {
            quote! {V}
        };
        let mut v = quote! {()};
        if self.kind.reduce {
            v = quote! {<#visitor as Monoid>::T}
        };
        if self.kind.short_circuiting {
            v = quote! {std::ops::ControlFlow<#visitor::Error, #v>}
        };
        v
    }
    fn generate_arm(&self, ident: TokenStream, fields: &Fields) -> TokenStream {
        let idents = field_typed_idents(fields.iter());
        let payload = fields_to_payload(fields);
        let mut any_real_visit = false;
        let visits = idents
            .iter()
            .map(|(id, ty)| {
                let ty = Ty::interpret(ty.clone(), &|ty| self.visitable_ty(ty));
                match ty {
                    Some(ty) => {
                        let first = !any_real_visit;
                        any_real_visit = true;
                        self.visit_expr(parse_quote!(#id), &ty, first)
                    }
                    None => parse_quote!(),
                }
            })
            .collect::<Vec<_>>();
        let visitor_reduce_value = self.kind.reduce.then_some(quote! {
            let mut visitor_reduce_value: <V as Monoid>::T;
        });
        let return_value = {
            let mut v = quote! {()};
            if self.kind.reduce {
                v = quote! {visitor_reduce_value}
            };
            if self.kind.short_circuiting {
                v = quote! {std::ops::ControlFlow::Continue(#v)}
            };
            v
        };
        if any_real_visit {
            quote! {
                #ident #payload => {
                    #visitor_reduce_value
                    #(#visits)*
                    #return_value
                }
            }
        } else {
            let v = self.default_value();
            quote! {#ident {..} => #v,}
        }
    }
    fn default_value(&self) -> TokenStream {
        let mut v = quote! {()};
        if self.kind.reduce {
            v = quote! {V::identity()}
        };
        if self.kind.short_circuiting {
            v = quote! {std::ops::ControlFlow::Continue(#v)}
        };
        v
    }
    fn visit_expr(&self, e: syn::Expr, ty: &Ty, first: bool) -> TokenStream {
        let deref = if self.kind.map {
            quote! {deref_mut}
        } else {
            quote! {deref}
        };
        match ty {
            Ty::Vec(ty) => {
                let body = self.visit_expr(parse_quote!(visitor_item), ty, false);
                let intialize_visitor_reduce_value = (first && self.kind.reduce)
                    .then_some(quote! {visitor_reduce_value = V::identity();});
                quote!(
                    #intialize_visitor_reduce_value
                    for visitor_item in #e {
                        #body
                    }
                )
            }
            Ty::Box(ty) => self.visit_expr(parse_quote!(#e.#deref()), ty, first),
            Ty::Tuple(items) => {
                let named_types: Vec<_> = items
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| {
                        (
                            Ident::new(&format!("visitor_item_{i}"), Span::call_site()),
                            ty,
                        )
                    })
                    .collect();

                let vars: Vec<_> = named_types.iter().map(|(id, _)| id).collect();
                let exprs: Vec<_> = named_types
                    .iter()
                    .map(|(id, ty)| self.visit_expr(parse_quote!(#id), ty, false))
                    .collect();
                quote!(
                    {
                        let (#(#vars),*) = #e;
                        #(#exprs;)*
                    };
                )
            }
            Ty::Ident(ident) => {
                let function = self.visit_function_name(ident);

                let qm = self.kind.short_circuiting.then_some(Some(quote! {?}));
                let mut e = quote!(visitor.#function(#e)#qm);
                if self.kind.reduce {
                    if first {
                        e = quote!(visitor_reduce_value = #e);
                    } else {
                        e = quote!(V::append(&mut visitor_reduce_value, #e))
                    }
                };
                println!("{}", quote!(#e;).to_token_stream());
                e = quote!(#e;);
                e
            }
        }
    }
}

pub(crate) fn main() {
    let hax_sources = get_hax_sources();
    let types = &{
        let mut visitable_items = VisitableCollector::default();
        visitable_items.visit_file(&hax_sources);
        visitable_items.items
    };
    let mut modules = vec![];
    let mut manual_drivers = vec![];
    for short_circuiting in [true, false] {
        for map in [true, false] {
            for reduce in [true, false] {
                let kind = VisitorKind {
                    short_circuiting,
                    map,
                    reduce,
                };
                let make_visitor = VisitorBuilder { kind, types };
                modules.push(make_visitor.generate_module(&mut manual_drivers));
            }
        }
    }
    let file = quote! {#(#modules)*};
    crate::write(&file, "src/ast/generated/visitor.rs");
    let file = quote! {#(#manual_drivers)*};
    crate::write(&file, "src/ast/generated/visitor_manual_template.rs");
}
