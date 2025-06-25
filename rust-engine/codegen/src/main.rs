use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    parse_quote, visit::Visit, visit_mut::VisitMut, Attribute, Fields, File, Ident, ItemEnum,
    ItemStruct, Meta, PathArguments,
};

mod helpers;
mod inline_mods;
use helpers::*;

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
    pub options: Option<VisitableOptions>,
    pub ident: Ident,
    pub kind: VisitableItemKind,
}

/// Walks a `syn::File` and collects every `(VisitableKind, payload)`.
struct CollectVisitableItems {
    current_module: syn::Path,
    items: Vec<VisitableItem>,
}

impl Default for CollectVisitableItems {
    fn default() -> Self {
        Self {
            current_module: parse_quote!(crate),
            items: Default::default(),
        }
    }
}

impl CollectVisitableItems {
    fn insert(&mut self, kind: VisitableItemKind, attr_payload: TokenStream, ident: Ident) {
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
            options,
            ident,
            kind,
        });
    }
}

impl<'a> Visit<'a> for CollectVisitableItems {
    fn visit_item_mod(&mut self, i: &'a syn::ItemMod) {
        let prev_module = self.current_module.clone();
        let i_ident = &i.ident;
        self.current_module = parse_quote!(#prev_module :: #i_ident);
        syn::visit::visit_item_mod(self, i);
        self.current_module = prev_module.clone();
    }
    fn visit_item_struct(&mut self, node: &ItemStruct) {
        if let Some(payload) = find_visitable_attr_tokens(&node.attrs) {
            self.insert(
                VisitableItemKind::Struct(node.clone()),
                payload,
                node.ident.clone(),
            );
        }
        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &ItemEnum) {
        if let Some(payload) = find_visitable_attr_tokens(&node.attrs) {
            self.insert(
                VisitableItemKind::Enum(node.clone()),
                payload,
                node.ident.clone(),
            );
        }
        syn::visit::visit_item_enum(self, node);
    }
}

fn find_visitable_attr_tokens(attrs: &[Attribute]) -> Option<TokenStream> {
    attrs.iter().find_map(|attr| match &attr.meta {
        Meta::List(m) if m.path.is_ident("visitable") => Some(m.tokens.clone()),
        Meta::Path(path) if path.is_ident("visitable") => Some(quote! {}),
        _ => None,
    })
}

fn load_source_file_with_inlining() -> File {
    let mut module = read("../src/lib.rs");
    let mut inliner = inline_mods::ModuleInliner::new("../src");
    inliner.visit_file_mut(&mut module);
    module
}

#[derive(Copy, Clone, Debug)]
struct VisitorKind {
    /// Can this visitor short circuit control flow?
    pub short_circuiting: bool,
    /// When visiting a type (say `Expr`), do we take a `&mut Expr` (then `map` is true) or a `&'a Expr`?
    pub mutable: bool,
    /// Visitor returns some value (the type must be a monoid)
    pub reduce: bool,
}

struct VisitorBuilder<'a> {
    /// The kind of visitor we are building
    pub kind: VisitorKind,
    /// Types allowed to be visited
    pub types: &'a Vec<VisitableItem>,
    /// Templates for manual drivers implementation
    pub manual_drivers_templates: Vec<TokenStream>,
}

/// Types that we recognize.
#[derive(Clone)]
enum Ty {
    /// A vector
    Vec(Box<Ty>),
    /// A box
    Box(Box<Ty>),
    /// A tuple
    Tuple(Vec<Ty>),
    /// An identifier
    Ident(Ident),
    /// An irrelevant type
    Erased,
}

impl From<syn::Type> for Ty {
    fn from(ty: syn::Type) -> Self {
        if let syn::Type::Tuple(tuple) = ty {
            return Ty::Tuple(
                tuple
                    .elems
                    .into_iter()
                    .map(|t| Ty::from(t))
                    .collect::<Vec<_>>(),
            );
        }
        let syn::Type::Path(type_path) = ty else {
            unimplemented!("Other types than path types are not supported yet")
        };
        let Some(last) = type_path.path.segments.iter().last() else {
            unimplemented!("Qualified types are not supported, please `use`.")
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
            ("Vec", [t]) => Ty::Vec(Box::new(Ty::from(t.clone()))),
            ("Box", [t]) => Ty::Box(Box::new(Ty::from(t.clone()))),
            _ => Self::Ident(last.ident.clone()),
        }
    }
}

impl Ty {
    /// Is this type erased?
    fn erased(&self) -> bool {
        matches!(self, Ty::Erased)
    }
    /// Apply `f` repeatdely in every nested type
    fn map(self, f: &impl Fn(Self) -> Self) -> Self {
        f(match self {
            Ty::Vec(ty) => Ty::Vec(Box::new(ty.map(f))),
            Ty::Box(ty) => Ty::Box(Box::new(ty.map(f))),
            Ty::Tuple(items) => {
                let items = items.into_iter().map(|ty| ty.map(f)).collect();
                Ty::Tuple(items)
            }
            ty => ty,
        })
    }
    /// Normalize the type: bubble up erased value to root or nearest tuple.
    /// E.g. `(Erased, Erased)` is reduced to `Erased` while `(T, Erased)` is stuck.
    fn norm(self) -> Self {
        self.erase_when(&|ty| match ty {
            Ty::Vec(ty) | Self::Box(ty) => ty.erased(),
            Ty::Tuple(items) => items.into_iter().all(Ty::erased),
            ty => ty.erased(),
        })
    }
    /// Erase type (at any level of nest) when predicate `f` holds
    fn erase_when(self, f: &impl Fn(&Self) -> bool) -> Self {
        self.map(&|ty| if f(&ty) { Self::Erased } else { ty })
    }
}

impl VisitorKind {
    /// Computes the components of the name of this visitor kind.
    fn name_components(&self) -> Vec<&str> {
        let components: Vec<_> = vec![
            self.mutable.then_some("map"),
            self.reduce.then_some("reduce"),
            self.short_circuiting.then_some("cf"),
        ]
        .into_iter()
        .flatten()
        .collect();
        if components.is_empty() {
            vec!["vanilla"]
        } else {
            components
        }
    }
    /// Compute the string idenitfier used to target a specific visitor kind in an attribute.
    fn kind(&self) -> String {
        self.name_components().join("_")
    }
    /// Compute the name of the module for this visitor kind.
    fn module_name(&self) -> Ident {
        let name = self.name_components().join("_");
        Ident::new(&name, Span::call_site())
    }
    /// Compute the trait name for this visitor kind.
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
    /// The trait-level generics for this visitor kind.
    fn trait_generics(&self) -> syn::Generics {
        if self.mutable {
            parse_quote! {<>}
        } else {
            parse_quote! {<'lt>}
        }
    }
    /// How should we borrow AST nodes in this visitor?
    fn borrow(&self) -> TokenStream {
        if self.mutable {
            quote! {&mut}
        } else {
            quote! {&'lt}
        }
    }
    /// Compute the return type of visitor methods or driver functions for this visitor kind.
    fn return_type(&self, from_method: bool) -> TokenStream {
        let visitor = if from_method {
            quote! {Self}
        } else {
            quote! {V}
        };
        let mut v = quote! {()};
        if self.reduce {
            v = quote! {#visitor::Out}
        };
        if self.short_circuiting {
            v = quote! {std::ops::ControlFlow<#visitor::Error, #v>}
        };
        v
    }
    /// Compute the default return value for this visitor kind. Should inhabit the type produced by `self.return_type()`.
    fn default_return_value(&self) -> TokenStream {
        let mut v = quote! {()};
        if self.reduce {
            v = quote! {V::Out::identity()}
        };
        if self.short_circuiting {
            v = quote! {std::ops::ControlFlow::Continue(#v)}
        };
        v
    }
    /// Computes a description for this visitor.
    fn description(&self) -> String {
        let sentences = vec![
            Some(match self.reduce {
                true => "Map visitor for the abstract syntax tree of hax".into(),
                false => "Fold visitor for the abstract syntax tree of hax".into(),
            }),
            Some(format!(
                "Visits {}nodes of each type of the AST",
                if self.mutable { "mutable " } else { "" }
            )),
            self.short_circuiting
                .then_some(format!("Each visiting function may break control flow")),
        ];
        sentences
            .iter()
            .flatten()
            .map(|s| format!("{s}."))
            .collect::<Vec<_>>()
            .join(" ")
    }
    /// Computes a `doc` attribute for this visitor.
    fn doc(&self) -> TokenStream {
        let doc = self.description();
        quote! {#[doc=#doc]}
    }
}

impl<'a> VisitorBuilder<'a> {
    /// Is this type visitable?
    fn visitable_ty(&self, ty: &Ident) -> bool {
        self.types.iter().any(|item| &item.ident == ty)
    }
    /// Computes the name of a visit function or method
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
    /// Computes the name of a (manual!) visit function or method.
    /// This happens when a type is marked `#[visitable(manual_driver(...))]`.
    fn visit_function_name_manual(&self, ty: &Ident) -> Ident {
        let fun_name = self.visit_function_name(ty).to_string();
        let mod_name = self.kind.module_name();
        Ident::new(&format!("manual_{mod_name}_{fun_name}"), Span::call_site())
    }
    fn push_manual_drivers_template(&mut self, _ident: &Ident, template: TokenStream) {
        self.manual_drivers_templates.push(template)
    }
    /// Generate the whole visitor module.
    fn generate_module(&mut self) -> TokenStream {
        let types = self.types.as_slice();
        let trait_definition = self.generate_trait(types);
        let driver_functions = self.generate_driver_functions(types);
        let module_name = self.kind.module_name();
        quote! {
            pub mod #module_name {
                use super::*;
                #trait_definition
                #driver_functions
            }
        }
    }
    /// Generate the driver functions associated to the visitor being generated.
    fn generate_driver_functions(&mut self, items: &[VisitableItem]) -> TokenStream {
        let methods: Vec<_> = items
            .iter()
            .map(|item| self.generate_driver_function(item))
            .collect();
        quote! {#(#methods)*}
    }
    /// Generate one method of the visitor trait.
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
    /// Generates the trait of the visitor being generated.
    fn generate_trait(&self, items: &[VisitableItem]) -> TokenStream {
        let trait_name = self.kind.trait_name();
        let trait_generics = self.kind.trait_generics();
        let methods: Vec<_> = items
            .iter()
            .map(|item| self.generate_method(item))
            .collect();
        let assoc_error_type = self.kind.short_circuiting.then_some(quote! {type Error;});
        let assoc_out_type = self.kind.reduce.then_some(quote! {type Out: Monoid;});
        let doc = self.kind.doc();
        quote! {
            #doc
            pub trait #trait_name #trait_generics {
                #assoc_error_type #assoc_out_type
                #(#methods)*
            }
        }
    }
    /// The signature of a driver function (if `from_method`) or a visitor method (if `!form_method`).
    /// When `manual` is true, the name fo the function is dervied using `visit_function_name_manual`.
    fn signature(&self, item: &VisitableItem, from_method: bool, manual: bool) -> TokenStream {
        let method = if manual {
            self.visit_function_name_manual(&item.ident)
        } else {
            self.visit_function_name(&item.ident)
        };
        let borrow = self.kind.borrow();
        let self_ty = &item.ident;
        let ret = self.kind.return_type(from_method);
        if from_method {
            quote! {fn #method(&mut self, v: #borrow #self_ty) -> #ret}
        } else {
            let trait_name = self.kind.trait_name();
            let trait_generics = self.kind.trait_generics();
            let visitor_generics: syn::Generics =
                parse_quote!(<V: #trait_name #trait_generics + ?Sized>);
            let generics = merge_generics(trait_generics, visitor_generics);
            quote! {pub fn #method #generics(visitor: &mut V, v: #borrow #self_ty) -> #ret}
        }
    }
    /// Generate a driver function.
    /// A driver function takes two arguments: a visitor (a value of type `impl TheVisitorBeingDerived`) and a value of type `T`.
    /// Such a driver function destructs structurally one level of `T` and visits each subvalue, using the supplied visitor.
    /// Concretely, it will repetedly call methods from the visitor. In turn, the visitor calls driver functions.
    fn generate_driver_function(&mut self, item: &VisitableItem) -> TokenStream {
        let type_ident = &item.ident;
        let sig = self.signature(item, false, false);
        match &item.options {
            Some(VisitableOptions::ManualDerive(target))
                if target.len() == 0 || target.contains(&self.kind.kind()) =>
            {
                let manual_driver = self.visit_function_name_manual(&item.ident);
                let sig_manual_driver = self.signature(item, false, true);
                self.push_manual_drivers_template(
                    &manual_driver,
                    quote! {#sig_manual_driver {todo!()}},
                );
                return quote! {
                    #sig {
                        #manual_driver(visitor, v)
                    }
                };
            }
            Some(VisitableOptions::Opaque) => {
                let v = self.kind.default_return_value();
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
        let catchall = arms
            .is_empty()
            .then_some(quote! {_ => unreachable!("references are always considered inhabited, even for an empty enum")});
        quote! {
            #[allow(unused)] #sig {
                match v {
                    #(#arms)*
                    #catchall
                }
            }
        }
    }
    // Generate a match arm that destructs a variant or struct named `ident` and visit each of its sub values.
    fn generate_arm(&self, ident: TokenStream, fields: &Fields) -> TokenStream {
        let idents = field_typed_idents(fields.iter());
        let payload = fields_to_payload(fields);
        let mut any_real_visit = false;
        let visits = idents
            .iter()
            .map(|(id, ty)| {
                let mut ty = Ty::from(ty.clone());
                ty = ty
                    .erase_when(&|ty| match ty {
                        Ty::Ident(ident) => !self.visitable_ty(&ident),
                        _ => false,
                    })
                    .norm();
                match ty {
                    Ty::Erased => parse_quote!(),
                    ty => {
                        let first = !any_real_visit;
                        any_real_visit = true;
                        self.generate_visit_expr(parse_quote!(#id), &ty, first)
                    }
                }
            })
            .collect::<Vec<_>>();
        let visitor_reduce_value = self.kind.reduce.then_some(quote! {
            let mut visitor_reduce_value: V::Out;
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
            let v = self.kind.default_return_value();
            quote! {#ident {..} => #v,}
        }
    }
    /// Generate an expression that visits the expression `e` of type `ty`.
    fn generate_visit_expr(&self, e: syn::Expr, ty: &Ty, first: bool) -> TokenStream {
        let deref = if self.kind.mutable {
            quote! {deref_mut}
        } else {
            quote! {deref}
        };
        match ty {
            Ty::Vec(ty) => {
                let body = self.generate_visit_expr(parse_quote!(visitor_item), ty, false);
                let intialize_visitor_reduce_value = (first && self.kind.reduce)
                    .then_some(quote! {visitor_reduce_value = V::Out::identity();});
                quote!(
                    #intialize_visitor_reduce_value
                    for visitor_item in #e {
                        #body
                    }
                )
            }
            Ty::Box(ty) => self.generate_visit_expr(parse_quote!(#e.#deref()), ty, first),
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
                    .map(|(id, ty)| self.generate_visit_expr(parse_quote!(#id), ty, false))
                    .collect();
                quote!(
                    {
                        let (#(#vars),*) = #e;
                        #(#exprs)*
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
                        e = quote!(visitor_reduce_value.append(#e))
                    }
                };
                quote!(#e;)
            }
            Ty::Erased => quote!(();),
        }
    }
}

pub(crate) fn main() {
    let hax_sources = load_source_file_with_inlining();
    let types = &{
        let mut visitable_items = CollectVisitableItems::default();
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
                    mutable: map,
                    reduce,
                };
                let mut make_visitor = VisitorBuilder {
                    kind,
                    types,
                    manual_drivers_templates: vec![],
                };
                modules.push(make_visitor.generate_module());
                manual_drivers.extend_from_slice(&make_visitor.manual_drivers_templates);
            }
        }
    }
    let file = quote! {#(#modules)*};
    write(&file, "../src/ast/visitors/generated.rs");
    let file = quote! {#(#manual_drivers)*};
    write(&file, "../src/ast/visitors/generated_manual_templates.rs");
}
