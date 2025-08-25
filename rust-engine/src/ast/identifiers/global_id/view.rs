#![allow(unused)]

use std::iter::Peekable;

use hax_frontend_exporter::{DefKind, DefPathItem, DisambiguatedDefPathItem, ImplInfos};
use itertools::Itertools;
use thiserror::Error;

use crate::{ast::identifiers, symbol::Symbol};
type Disambiguator = u32;

type SymbolPosition = u8;
const TYPE_NS: SymbolPosition = 0;
const VALUE_NS: SymbolPosition = 1;
const MACRO_NS: SymbolPosition = 2;
const LIFETIME_NS: SymbolPosition = 3;
const NONE: SymbolPosition = 4;
const TYPE_NS_OR_CRATE: SymbolPosition = 5;

fn symbol_position_name(s: SymbolPosition) -> &'static str {
    match s {
        TYPE_NS => "TYPE_NS",
        VALUE_NS => "VALUE_NS",
        MACRO_NS => "MACRO_NS",
        LIFETIME_NS => "LIFETIME_NS",
        NONE => "NONE",
        _ => unreachable!(),
    }
}

#[derive(Clone)]
struct Ref<const SP: SymbolPosition> {
    identifier: super::DefId,
}

impl<const SP: SymbolPosition> Ref<SP> {
    fn last_path_item(&self) -> Result<&DisambiguatedDefPathItem, Error> {
        self.identifier.path.last().ok_or(Error::ParentNotFound)
    }
    pub fn disambiguator_opt(&self) -> Result<Disambiguator, Error> {
        let last_path_item = self.last_path_item();
        if SP == TYPE_NS_OR_CRATE && last_path_item.is_err() {
            return Ok(0);
        }
        Ok(last_path_item?.disambiguator)
    }
    fn name_opt(&self) -> Result<Option<Symbol>, Error> {
        let last_path_item = self.last_path_item();
        if SP == TYPE_NS_OR_CRATE && last_path_item.is_err() {
            return Ok(Some(Symbol::new(&self.identifier.krate)));
        }
        let s = match &self.last_path_item()?.data {
            DefPathItem::TypeNs(s) if SP == TYPE_NS => s,
            DefPathItem::ValueNs(s) if SP == VALUE_NS => s,
            DefPathItem::MacroNs(s) if SP == MACRO_NS => s,
            DefPathItem::LifetimeNs(s) if SP == LIFETIME_NS => s,
            _ if SP == NONE => return Ok(None),
            got => {
                let got = got.clone();
                return Err(Error::WrongSymbolPosition { expected: SP, got });
            }
        };
        Ok(Some(Symbol::new(&s)))
    }
    fn check_invariant(&self) -> Result<(), Error> {
        self.name_opt().map(|_| ())
    }
}

trait ContainsSymbol<const SP: SymbolPosition> {}
impl ContainsSymbol<TYPE_NS> for () {}
impl ContainsSymbol<VALUE_NS> for () {}
impl ContainsSymbol<MACRO_NS> for () {}
impl ContainsSymbol<LIFETIME_NS> for () {}
impl ContainsSymbol<TYPE_NS_OR_CRATE> for () {}

impl<const SP: SymbolPosition> Ref<SP>
where
    (): ContainsSymbol<SP>,
{
    fn disambiguator(&self) -> Disambiguator {
        self.disambiguator_opt().unwrap_or_else(|_| unreachable!("`self.name()` returns `Some(_)`, this implies `self.disambiguator_opt()` to return `Some(_)` as well."))
    }
    fn name(&self) -> Symbol {
        self.name_opt()
            .unwrap_or_else(|err| panic!("{err}"))
            // We know SP is TYPE_NS, VALUE_NS, MACRO_NS or LIFETIME_NS, thus `name_opt` should return Err(_) or Ok(Some(_))
            .unwrap()
    }
}

impl<const SP: SymbolPosition> Ref<SP> {
    pub fn new(identifier: impl AsRef<super::DefId>) -> Result<Self, Error> {
        let unchecked = Self {
            identifier: identifier.as_ref().clone(),
        };
        unchecked.check_invariant()?;
        Ok(unchecked)
    }
}

impl AsRef<super::DefId> for super::ExplicitDefId {
    fn as_ref(&self) -> &super::DefId {
        &self.def_id
    }
}

/// A module/crate only path. This is the `mod` longest suffix of a definition identifier path.
struct ModulePath(Vec<Ref<TYPE_NS>>);

enum ImplKind {
    Inherent,
    Trait,
}

#[derive(strum_macros::EnumIter)]
enum TypeDefinitionKind {
    Struct,
    Enum,
    Union,
}

#[derive(Clone)]
enum TypeDefinition {
    Struct(Ref<TYPE_NS>),
    Enum(Ref<TYPE_NS>),
    Union(Ref<TYPE_NS>),
}

impl From<&TypeDefinition> for Ref<TYPE_NS> {
    fn from(value: &TypeDefinition) -> Self {
        let (TypeDefinition::Struct(r) | TypeDefinition::Enum(r) | TypeDefinition::Union(r)) =
            value;
        r.clone()
    }
}

impl From<&TypeDefinition> for TypeDefinitionKind {
    fn from(value: &TypeDefinition) -> Self {
        match value {
            TypeDefinition::Struct(_) => Self::Struct,
            TypeDefinition::Enum(_) => Self::Enum,
            TypeDefinition::Union(_) => Self::Union,
        }
    }
}

impl From<TypeDefinition> for TypeDefinitionKind {
    fn from(value: TypeDefinition) -> Self {
        (&value).into()
    }
}

struct Constructor {
    name: Ref<TYPE_NS>,
    parent: TypeDefinition,
}

// struct AssociatedItem<Name = DisambiguatedSymbol, Disambiguator = Disambiguator> {
enum AssociatedItem {
    Fn(Ref<VALUE_NS>),
    Const(Ref<VALUE_NS>),
    Type(Ref<TYPE_NS>),
}

enum AssocParent {
    Impl {
        def_id: Ref<NONE>,
        kind: ImplKind,
        impl_infos: Option<ImplInfos>,
    },
    Trait {
        name: Ref<TYPE_NS>,
        trait_alias: bool,
    },
}

impl From<AssocParent> for Chunk {
    fn from(assoc_parent: AssocParent) -> Self {
        Self::AssocParent(assoc_parent)
    }
}

impl From<Constructor> for Chunk {
    fn from(constructor: Constructor) -> Self {
        Self::Constructor(constructor)
    }
}
impl From<TypeDefinition> for Chunk {
    fn from(td: TypeDefinition) -> Self {
        Self::TypeDefinition(td)
    }
}

enum Chunk {
    TypeDefinition(TypeDefinition),
    Constructor(Constructor),
    AssocParent(AssocParent),
    AssociatedItem {
        item: AssociatedItem,
        parent: AssocParent,
    },
    Fn(Ref<VALUE_NS>),
    Const(Ref<VALUE_NS>),
    Use(Ref<NONE>),
    AnonConst(Ref<NONE>),
    InlineConst(Ref<NONE>),
    // (** This is e.g.: {[
    //     const {
    //         fn f() {}
    //     }
    //   ]}
    //   Here, `f` is under an `InlineConst`.
    //   *)
    TraitAlias(Ref<TYPE_NS>),
    Foreign(Ref<NONE>),
    ForeignTy(Ref<TYPE_NS>),
    TyAlias(Ref<TYPE_NS>),
    ExternCrate(Ref<TYPE_NS>),
    Opaque(Ref<NONE>),
    // (** This is e.g.: {[
    //   fn f() -> impl Clone {}
    //   fn g() {
    //     f();
    //   }
    // ]}
    // Here, the type of `f()` is `<f::OpaqueTy>`.
    // *)
    Static(Ref<VALUE_NS>),
    Macro(Ref<MACRO_NS>),
    Mod(Ref<TYPE_NS>),
    GlobalAsm(Ref<NONE>),
    Field {
        name: Ref<VALUE_NS>,
        parent: Constructor,
    },
    Closure(Ref<NONE>),
}

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error(
        "Expected a path item data of kind {}, got {:#?}",
        symbol_position_name(*expected),
        got
    )]
    WrongSymbolPosition {
        expected: SymbolPosition,
        got: DefPathItem,
    },
    #[error("Expected a parent, found none.")]
    ParentNotFound,
    #[error(
        "Expected a non (TyParam | ConstParam | InlineConst | PromotedConst | \
           LifetimeParam | SyntheticCoroutineBody) identifier, got {0:#?}"
    )]
    UnreachableDefKind(super::DefId),
}

trait FromDefId: Sized {
    fn from_def_id(def_id: &mut impl Iterator<Item = super::ExplicitDefId>) -> Result<Self, Error>;
}

// #[derive(Clone)]
// struct ExplicitDefIdIterator(Option<super::ExplicitDefId>);

// impl Iterator for ExplicitDefIdIterator {
//     type Item = super::ExplicitDefId;

//     fn next(&mut self) -> Option<Self::Item> {
//         let current = self.0.clone()?;
//         self.0 = self.compute_next_value();
//         Some(current)
//     }
// }

// impl ExplicitDefIdIterator {
//     pub fn new(def_id: super::ExplicitDefId) -> Self {
//         Self(Some(def_id))
//     }
//     pub fn next_result(&mut self) -> Result<super::ExplicitDefId, Error> {
//         self.next().ok_or(Error::ParentNotFound)
//     }

//     fn compute_next_value(&self) -> Option<super::ExplicitDefId> {
//         let def_id = &self.0.as_ref()?.def_id;
//         let is_constructor = matches!(&def_id.kind, DefKind::Field);
//         Some(super::ExplicitDefId {
//             is_constructor,
//             def_id: def_id.parent.as_ref()?.as_ref().clone(),
//         })
//     }
//     pub fn peek(&self) -> Option<&super::ExplicitDefId> {
//         self.0.as_ref()
//     }
// }
#[extension_traits::extension(trait ExtExplicitDefId)]
impl super::ExplicitDefId {
    fn drop_constructor(&self) -> Self {
        Self {
            is_constructor: false,
            ..self.clone()
        }
    }
}

impl FromDefId for AssocParent {
    fn from_def_id(def_id: &mut impl Iterator<Item = super::ExplicitDefId>) -> Result<Self, Error> {
        todo!()
    }
}
impl FromDefId for Constructor {
    fn from_def_id(def_id: &mut impl Iterator<Item = super::ExplicitDefId>) -> Result<Self, Error> {
        todo!()
    }
}

impl FromDefId for TypeDefinition {
    fn from_def_id(it: &mut impl Iterator<Item = super::ExplicitDefId>) -> Result<Self, Error> {
        let def_id = it.next().ok_or(Error::ParentNotFound)?;
        macro_rules! name {
            () => {
                Ref::new(&def_id)?
            };
        }
        Ok(match &def_id.def_id.kind {
            DefKind::Union => TypeDefinition::Union(name!()),
            DefKind::Struct => TypeDefinition::Struct(name!()),
            DefKind::Enum => TypeDefinition::Enum(name!()),
            _ => Err(Error::UnreachableDefKind(def_id.def_id.clone()))?,
        })
    }
}

impl FromDefId for Chunk {
    fn from_def_id(it: &mut impl Iterator<Item = super::ExplicitDefId>) -> Result<Self, Error> {
        let def_id = it.next().ok_or(Error::ParentNotFound)?;
        macro_rules! name {
            () => {
                Ref::new(&def_id)?
            };
        }
        use hax_frontend_exporter::{CtorOf, DefKind};
        let chunk = match &def_id.def_id.kind {
            DefKind::TyParam
            | DefKind::ConstParam
            | DefKind::PromotedConst
            | DefKind::LifetimeParam
            | DefKind::SyntheticCoroutineBody => {
                Err(Error::UnreachableDefKind(def_id.def_id.clone()))?
            }
            DefKind::Ctor(CtorOf::Struct, _) | DefKind::Struct if def_id.is_constructor => {
                Self::Constructor(Constructor {
                    name: name!(),
                    parent: TypeDefinition::Struct(Ref::new(def_id.drop_constructor())?),
                })
            }
            DefKind::Variant | DefKind::Ctor(_, _) => Self::Constructor(Constructor {
                name: name!(),
                parent: TypeDefinition::from_def_id(it)?,
            }),
            DefKind::Fn => Self::Fn(name!()),
            DefKind::Const => Self::Const(name!()),
            DefKind::Mod => Self::Mod(name!()),
            DefKind::Union => TypeDefinition::Union(name!()).into(),
            DefKind::Struct => TypeDefinition::Struct(name!()).into(),
            DefKind::Enum => TypeDefinition::Enum(name!()).into(),
            DefKind::Impl { of_trait } => AssocParent::Impl {
                def_id: name!(),
                kind: if *of_trait {
                    ImplKind::Trait
                } else {
                    ImplKind::Inherent
                },
                // TODO: this is wrong.
                // We need more information from the OCaml engine.
                impl_infos: None,
            }
            .into(),
            DefKind::Trait => AssocParent::Trait {
                name: name!(),
                trait_alias: false,
            }
            .into(),
            DefKind::TraitAlias => AssocParent::Trait {
                name: name!(),
                trait_alias: true,
            }
            .into(),
            DefKind::TyAlias => Self::TyAlias(name!()),
            DefKind::ForeignTy => Self::ForeignTy(name!()),
            DefKind::AssocTy => Self::AssociatedItem {
                item: AssociatedItem::Type(name!()),
                parent: AssocParent::from_def_id(it)?,
            },
            DefKind::AssocFn => Self::AssociatedItem {
                item: AssociatedItem::Fn(name!()),
                parent: AssocParent::from_def_id(it)?,
            },
            DefKind::AssocConst => Self::AssociatedItem {
                item: AssociatedItem::Const(name!()),
                parent: AssocParent::from_def_id(it)?,
            },
            DefKind::Static { .. } => Self::Static(name!()),
            DefKind::Macro(_) => Self::Macro(name!()),
            DefKind::ExternCrate => Self::ExternCrate(name!()),
            DefKind::Use => Self::Use(name!()),
            DefKind::ForeignMod => Self::Foreign(name!()),
            DefKind::AnonConst => Self::AnonConst(name!()),
            DefKind::InlineConst => Self::InlineConst(name!()),
            DefKind::OpaqueTy => Self::Opaque(name!()),
            DefKind::Field => Self::Field {
                name: todo!(),
                parent: Constructor::from_def_id(it)?,
            },
            DefKind::GlobalAsm => Self::GlobalAsm(name!()),
            DefKind::Closure => Self::Closure(name!()),
        };
        Ok(chunk)
    }
}

struct View {
    module_path: Vec<Ref<TYPE_NS_OR_CRATE>>,
    relative_path: Vec<Chunk>,
}

impl From<super::ExplicitDefId> for View {
    fn from(def_id: super::ExplicitDefId) -> Self {
        let mut parents = def_id.parents().collect::<Vec<_>>();
        let modules = std::iter::from_fn(|| {
            parents.pop_if(|def_id| matches!(def_id.def_id.kind, DefKind::Mod))
        })
        .collect::<Vec<_>>();
        let mut it = parents.into_iter();

        let relative_path = std::iter::from_fn(|| match Chunk::from_def_id(&mut it) {
            Ok(value) => Some(value),
            Err(Error::ParentNotFound) => None,
            Err(err) => unreachable!("{err}"),
        })
        .collect();

        let module_path = modules
            .iter()
            .map(|def_id| Ref::new(def_id).unwrap_or_else(|err| unreachable!("{err}")))
            .collect();

        Self {
            module_path,
            relative_path,
        }
    }
}

#[derive(Clone)]
struct NamedFieldPrefix {
    // fixed_prefix: Option<Symbol>,
    add_constructor_name: bool,
    add_type_name: bool,
}

#[derive(Clone, Copy)]
struct ConstructorPrefix {
    add_type_name: bool,
}

#[derive(Clone)]
struct NamePolicy {
    reserved_keyword: fn(&str) -> bool,
    transform_anonymous_fields: fn(usize) -> String,
    prefix_constructors: fn(TypeDefinitionKind) -> ConstructorPrefix,
    prefix_named_fields: NamedFieldPrefix,
    prefix_associated_item_with_trait_name: bool,
}

struct Rendered {
    path: Vec<String>,
    name: String,
}

#[derive(derive_more::Display, strum_macros::EnumIter)]
enum Prefix {
    #[display("impl")]
    Impl,
    #[display("anon_const")]
    AnonConst,
    #[display("inline_const")]
    InlineConst,
    #[display("foreign")]
    Foreign,
    #[display("use")]
    Use,
    #[display("opaque")]
    Opaque,
    #[display("closure")]
    Closure,
    #[display("t")]
    Type,
    #[display("v")]
    Value,
    #[display("f")]
    AssociatedItem,
    #[display("i")]
    ImplLocalBound,
    #[display("discriminant")]
    Discriminant,
}

enum PrefixPolicyPredicate {
    /// Holds when the name to be rendered and the prefix to add have the same case.
    SameCase,
    /// Holds when the name to be rendered is a sub-name.
    NotRoot,
    /// Holds when the name to be rendered is the whole name.
    Root,
}

struct PrefixPolicy {
    /// What prefix should we add?
    prefix: Prefix,
    /// Add the prefix unless one predicate succeeds.
    unless: Vec<PrefixPolicyPredicate>,
}

enum NameDoc {
    Concat(Box<NameDoc>, Box<NameDoc>),
    Policy {
        policy: PrefixPolicy,
        doc: Box<NameDoc>,
    },
    String {
        trusted: bool,
        string: String,
    },
    Empty,
}

impl NamePolicy {
    fn concat(&self, l: &str, r: &str) -> String {
        todo!()
    }

    fn escape_prefixes(&self, s: &str) -> String {
        use strum::IntoEnumIterator;
        let prefixes = Prefix::iter()
            .map(|prefix| prefix.to_string())
            .collect::<Vec<_>>();
        match s.split_once("_") {
            Some(("", rest)) => format!("e_{}", self.escape_prefixes(rest)),
            Some((prefix, rest)) if prefixes.iter().any(|s| &*s == prefix) => {
                let first_char = prefix.chars().next().unwrap_or_else(|| unreachable!("prefixes are non empty, since `prefix` was found in `prefixes`, it cannot be found"));
                format!("{first_char}{prefix}_{}", self.escape_prefixes(rest))
            }
            _ => s.into(),
        }
    }
    /// Escape the separator `__`
    fn escape_separator(&self, s: &str) -> String {
        let mut chunks = s.split("_").map(&str::to_string).collect::<Vec<_>>();
        let len = chunks.len();
        for chunk in &mut chunks[1..len - 1] {
            if chunk.chars().all(|c| c == 'e') {
                *chunk += "e";
            }
        }
        chunks.join("_")
    }

    fn render_disambiguated(&self, name: impl AsRef<str>, disambiguator: u32) -> String {
        let name = name.as_ref();
        if disambiguator == 0 {
            name.to_string()
        } else {
            format!("{name}_{disambiguator}")
        }
    }
}

impl PrefixPolicyPredicate {
    fn eval(&self, rendered: &str, prefix: &str, root: bool) -> bool {
        match self {
            PrefixPolicyPredicate::SameCase => {
                fn same_first_case_ascii(a: &str, b: &str) -> bool {
                    match (a.chars().next(), b.chars().next()) {
                        (Some(ca), Some(cb)) => {
                            (ca.is_ascii_uppercase() && cb.is_ascii_uppercase())
                                || (ca.is_ascii_lowercase() && cb.is_ascii_lowercase())
                        }
                        _ => false,
                    }
                }
                same_first_case_ascii(rendered, prefix)
            }
            PrefixPolicyPredicate::NotRoot => !root,
            PrefixPolicyPredicate::Root => root,
        }
    }
}

impl PrefixPolicy {
    fn render(&self, rendered: String, root: bool) -> String {
        let prefix = self.prefix.to_string();
        for condition in &self.unless {
            if condition.eval(&rendered, &prefix, root) {
                return rendered;
            }
        }
        format!("{prefix}{rendered}")
    }
}

impl NameDoc {
    fn empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
    fn norm_step(&mut self, changed: &mut bool) {
        match self {
            Self::Concat(l, r) if l.empty() => {
                *changed = true;
                *self = std::mem::replace(&mut **r, Self::Empty);
            }
            Self::Concat(l, r) if r.empty() => {
                *changed = true;
                *self = std::mem::replace(&mut **l, Self::Empty);
            }
            Self::Policy { policy: _, doc } => {
                if doc.empty() {
                    *changed = true;
                    *self = Self::Empty;
                } else {
                    doc.norm_step(changed);
                }
            }
            Self::Concat(l, r) => {
                l.norm_step(changed);
                r.norm_step(changed);
            }
            _ => (),
        }
    }
    fn norm(&mut self) {
        let mut changed = false;
        loop {
            self.norm_step(&mut changed);
            if !changed {
                break;
            }
        }
    }
    fn render_recurse(&self, leftmost: bool, name_policy: &NamePolicy) -> String {
        match self {
            Self::Concat(l, r) => name_policy.concat(
                &l.render_recurse(leftmost, name_policy),
                &r.render_recurse(false, name_policy),
            ),
            Self::Policy { policy, doc } => {
                let rendered = doc.render_recurse(leftmost, name_policy);
                policy.render(rendered, leftmost)
            }
            Self::String {
                trusted: true,
                string,
            } => string.clone(),
            Self::String {
                trusted: false,
                string,
            } => name_policy.escape_separator(&name_policy.escape_prefixes(string)),
            Self::Empty => "".into(),
        }
    }
    pub fn render(&self, name_policy: &NamePolicy) -> String {
        self.render_recurse(true, name_policy)
    }
}

impl<const SP: SymbolPosition> Ref<SP>
where
    (): ContainsSymbol<SP>,
{
    fn doc(&self, name_policy: &NamePolicy) -> NameDoc {
        NameDoc::String {
            trusted: false,
            string: self.render(name_policy),
        }
    }
    fn render(&self, name_policy: &NamePolicy) -> String {
        name_policy.render_disambiguated(self.name(), self.disambiguator())
    }
}

impl Ref<NONE> {
    fn doc(&self, prefix: Prefix, name_policy: &NamePolicy) -> NameDoc {
        let d = self.disambiguator_opt().unwrap_or(0);
        let doc = Box::new(NameDoc::String {
            trusted: false,
            string: format!("{d}"),
        });
        let policy = PrefixPolicy {
            prefix,
            unless: vec![],
        };
        NameDoc::Policy { policy, doc }
    }
}

impl NameDoc {
    fn prefix_unless_same_case(self, prefix: Prefix) -> Self {
        Self::Policy {
            policy: PrefixPolicy {
                prefix,
                unless: vec![],
            },
            doc: Box::new(self),
        }
    }
}

impl Chunk {
    fn render(&self, namespace: &[String], is_last_chunk: bool, policy: &NamePolicy) -> NameDoc {
        match self {
            Chunk::AssocParent(assoc_parent) => todo!(),
            Chunk::AssociatedItem { item, parent } => match item {
                AssociatedItem::Fn(_) => todo!(),
                AssociatedItem::Const(_) => todo!(),
                AssociatedItem::Type(_) => todo!(),
            },

            Chunk::Fn(r) | Chunk::Static(r) | Chunk::Const(r) => {
                r.doc(policy).prefix_unless_same_case(Prefix::Value)
            }
            Chunk::Macro(r) => r.doc(policy).prefix_unless_same_case(Prefix::Value),

            Chunk::Constructor(constructor) => {
                let mut string = constructor.name.render(policy);
                let typ = Ref::from(&constructor.parent);
                let options =
                    (policy.prefix_constructors)(TypeDefinitionKind::from(&constructor.parent));
                if options.add_type_name {
                    let type_name = typ.render(policy);
                    string = format!("{string}_{type_name}");
                };
                NameDoc::String {
                    trusted: false,
                    string,
                }
            }

            Chunk::Field { name, parent } => {
                if let Ok(index) = str::parse::<usize>(name.name().as_ref())
                    && name.disambiguator() == 0
                {
                    NameDoc::String {
                        trusted: true,
                        string: (policy.transform_anonymous_fields)(index),
                    }
                } else {
                    let mut string = name.render(policy);
                    let prefixes = &policy.prefix_named_fields;
                    if prefixes.add_constructor_name {
                        string = format!("{string}_{}", parent.name.render(policy));
                    }
                    if prefixes.add_type_name {
                        string = format!("{string}_{}", Ref::from(&parent.parent).render(policy));
                    }
                    NameDoc::String {
                        trusted: false,
                        string,
                    }
                }
            }

            Chunk::ExternCrate(r) | Chunk::ForeignTy(r) | Chunk::TraitAlias(r) | Chunk::Mod(r) => {
                r.doc(policy)
            }
            Chunk::TypeDefinition(td) => Ref::from(td).doc(policy),

            Chunk::Const(_) => todo!(),
            Chunk::Use(_) => todo!(),
            Chunk::AnonConst(_) => todo!(),
            Chunk::InlineConst(_) => todo!(),
            Chunk::Foreign(_) => todo!(),
            Chunk::TyAlias(_) => todo!(),
            Chunk::Opaque(_) => todo!(),
            Chunk::Static(_) => todo!(),
            Chunk::Macro(_) => todo!(),
            Chunk::GlobalAsm(_) => todo!(),
            Chunk::Closure(_) => todo!(),
        }
    }
}

mod helpers {
    use std::iter::Peekable;

    pub trait LastFlagExt: Iterator + Sized {
        fn with_last_flag(self) -> WithLastFlag<Self> {
            WithLastFlag {
                it: self.peekable(),
            }
        }
    }
    impl<I: Iterator> LastFlagExt for I {}

    pub struct WithLastFlag<I: Iterator> {
        it: Peekable<I>,
    }

    impl<I: Iterator> Iterator for WithLastFlag<I> {
        type Item = (I::Item, bool); // (item, is_last)

        fn next(&mut self) -> Option<Self::Item> {
            let item = self.it.next()?;
            let is_last = self.it.peek().is_none();
            Some((item, is_last))
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.it.size_hint()
        }
    }
}
use helpers::*;

impl NamePolicy {
    fn render(&self, def_id: super::GlobalId, name_policy: &NamePolicy) -> Rendered {
        let concrete_id = match def_id {
            super::GlobalId::Concrete(concrete_id) => concrete_id,
            super::GlobalId::Projector(concrete_id) => todo!(),
        };
        let view = View::from(concrete_id.def_id.clone());
        let path = view
            .module_path
            .iter()
            .map(|r| name_policy.render_disambiguated(r.name(), r.disambiguator()))
            .collect();
        let namespace = vec![];
        let name = view
            .relative_path
            .iter()
            .with_last_flag()
            .map(|(chunk, last)| chunk.render(&namespace[..], last, name_policy))
            .map(|doc| doc.render(name_policy))
            .join("__");
        Rendered { path, name }
    }
}
