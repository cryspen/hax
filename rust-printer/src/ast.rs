//! The core abstract syntax tree (AST) representation for hax.
//!
//! This module defines the primary data structures used to represent
//! typed syntax.
//!
//! The design of this AST is designed under the following constraints:
//!  1. Valid (cargo check) pretty-printed Rust can be produced out of it.
//!  2. The Rust THIR AST from the frontend can be imported into this AST.
//!  3. The AST defined in the OCaml engine can be imported into this AST.
//!  4. This AST can be exported to the OCaml engine.
//!  5. This AST should be suitable for AST transformations.

pub mod diagnostics;
// pub mod helper;
pub mod identifiers;
pub mod literals;
pub mod node;
pub mod span;

use std::marker::PhantomData;

pub use diagnostics::Diagnostic;
pub use identifiers::*;
pub use literals::*;
pub use node::Node;
pub use span::Span;

pub trait AstBounds:
    std::fmt::Debug + Clone + std::hash::Hash + Eq + PartialEq + PartialOrd + Ord
{
}
impl<T: std::fmt::Debug + Clone + std::hash::Hash + Eq + PartialEq + PartialOrd + Ord> AstBounds
    for T
{
}

#[macros::ast_derives]
pub enum Empty {}

pub trait AstTypes: AstBounds {
    type Wrapper<T: AstBounds>: AstBounds;
    type ExtExpr: AstBounds;
    type ExtPat: AstBounds;
    type ExtTy: AstBounds;
}

impl AstTypes for () {
    type Wrapper<T: AstBounds> = T;
    type ExtExpr = Empty;
    type ExtPat = Empty;
    type ExtTy = Empty;
}

type AstPosition = &'static str;
trait AstRetyper {
    type A: AstTypes;
    type B: AstTypes;
    fn retype_wrapper<T: AstBounds, U: AstBounds>(
        ast_position: AstPosition,
        node: &<Self::A as AstTypes>::Wrapper<T>,
        map: impl Fn(&T) -> U,
    ) -> <Self::B as AstTypes>::Wrapper<U>;
    fn retype_ext_expr(expr: <Self::A as AstTypes>::ExtExpr) -> <Self::B as AstTypes>::ExtExpr;
    fn retype_ext_pat(pat: <Self::A as AstTypes>::ExtPat) -> <Self::B as AstTypes>::ExtPat;
    fn retype_ext_ty(ty: <Self::A as AstTypes>::ExtTy) -> <Self::B as AstTypes>::ExtTy;
}

trait Retypable<RT: AstRetyper> {
    type Out;
    fn retype(&self, rt: &RT) -> Self::Out;
}

impl<RT: AstRetyper, T: Retypable<RT>, U: Retypable<RT>> Retypable<RT> for (T, U) {
    type Out = (T::Out, U::Out);
    fn retype(&self, rt: &RT) -> Self::Out {
        let (t, u) = self;
        (t.retype(rt), u.retype(rt))
    }
}

impl<RT: AstRetyper, T: Retypable<RT>> Retypable<RT> for Vec<T> {
    type Out = Vec<T::Out>;
    fn retype(&self, rt: &RT) -> Self::Out {
        self.iter().map(|item| item.retype(rt)).collect()
    }
}

impl<RT: AstRetyper, T: Retypable<RT>> Retypable<RT> for Box<T> {
    type Out = Box<T::Out>;
    fn retype(&self, rt: &RT) -> Self::Out {
        let value: &T = &*self;
        Box::new(value.retype(rt))
    }
}

macro_rules! identity_retypable_for {
    ($($ty:ty),*) => {
        $(impl<RT: AstRetyper> Retypable<RT> for $ty {
            type Out = $ty;
            fn retype(&self, _rt: &RT) -> Self::Out {
                self.clone()
            }
        })*
    };
}

identity_retypable_for!(GlobalId, bool, String, Diagnostic, LocalId);

// #[derive(macros::Retyper)]
pub enum Test<T: AstTypes = ()> {
    Hi(T::Wrapper<ExprKind<T>>),
}

impl < RT : AstRetyper > Retypable < RT > for GenericValue < RT :: A > where <
RT :: A as AstTypes > :: Wrapper < Ty < RT :: A > > : Retypable < RT, Out
= < RT :: B as AstTypes > :: Wrapper < Ty < < RT :: B > > >> , < RT :: A as
AstTypes > :: Wrapper < Expr < < RT :: A > > > : Retypable < RT, Out = < RT ::
B as AstTypes > :: Wrapper < Expr < < RT :: B > > >>
{
    type Out = GenericValue < RT :: B > ; fn
    retype(& self, retyper_instance : & RT) -> Self :: Out
    {
        match self
        {
            Self :: Ty(x0) =>
            { let x0 = x0.retype(retyper_instance); GenericValue :: Ty(x0) },
            Self :: Expr(x0) =>
            {
                let x0 = x0.retype(retyper_instance); GenericValue :: Expr(x0)
            }, Self :: Lifetime => { GenericValue :: Lifetime }
        }
    }
}

/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[macros::ast_derives]
pub enum GenericValue<T: AstTypes = ()> {
    /// A type-level generic value.
    /// Example: `i32` in `Vec<i32>`
    Ty(T::Wrapper<Ty<T>>),
    /// A const-level generic value.
    /// Example: `12` in `Foo<12>`
    Expr(T::Wrapper<Expr<T>>),
    /// A lifetime.
    /// Example: `'a` in `foo<'a>`
    Lifetime,
}

/// Built-in primitive types.
#[macros::ast_derives]
pub enum PrimitiveTy<T: AstTypes = ()> {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(T::Wrapper<IntKind>),
}

impl<RT: AstRetyper> Retypable<RT> for TyKind<RT::A>
where
    <RT::A as AstTypes>::Wrapper<PrimitiveTy<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<PrimitiveTy<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<Ty<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<Ty<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<GenericValue<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<GenericValue<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<Ty<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<Ty<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<Ty<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<Ty<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<Ty<RT::A>>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<Ty<RT::B>>>,
    <RT::A as AstTypes>::Wrapper<<RT::A as AstTypes>::ExtTy>:
        Retypable<RT, Out = <RT::B as AstTypes>::Wrapper<<RT::B as AstTypes>::ExtTy>>,
{
    type Out = TyKind<RT::B>;
    fn retype(&self, retyper_instance: &RT) -> Self::Out {
        match self {
            Self::Primitive(x0) => {
                let x0 = x0.retype(retyper_instance);
                TyKind::Primitive(x0)
            }
            Self::Tuple(x0) => {
                let x0 = x0.retype(retyper_instance);
                TyKind::Tuple(x0)
            }
            Self::App { head, args } => {
                let head = head.retype(retyper_instance);
                let args = args.retype(retyper_instance);
                TyKind::App { head, args }
            }
            Self::Arrow { inputs, output } => {
                let inputs = inputs.retype(retyper_instance);
                let output = output.retype(retyper_instance);
                TyKind::Arrow { inputs, output }
            }
            Self::Ref { inner, mutable } => {
                let inner = inner.retype(retyper_instance);
                let mutable = mutable.retype(retyper_instance);
                TyKind::Ref { inner, mutable }
            }
            Self::Error(x0) => {
                let x0 = x0.retype(retyper_instance);
                TyKind::Error(x0)
            }
            Self::Param(x0) => {
                let x0 = x0.retype(retyper_instance);
                TyKind::Param(x0)
            }
            Self::Ext(x0) => {
                let x0 = x0.retype(retyper_instance);
                TyKind::Ext(x0)
            }
        }
    }
}

/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[macros::ast_derives]
pub enum TyKind<T: AstTypes = ()> {
    /// A primitive type.
    /// Example: `i32`, `bool`
    Primitive(T::Wrapper<PrimitiveTy<T>>),

    /// A tuple type.
    /// Example: `(i32, bool)`
    Tuple(Vec<T::Wrapper<Ty<T>>>),

    /// A type application (generic type).
    /// Example: `Vec<i32>`
    App {
        head: GlobalId,
        args: Vec<T::Wrapper<GenericValue<T>>>,
    },

    /// A function or closure type.
    /// Example: `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow {
        inputs: Vec<T::Wrapper<Ty<T>>>,
        output: Box<T::Wrapper<Ty<T>>>,
    },

    /// A reference type.
    /// Example: `&i32`, `&mut i32`
    Ref {
        inner: Box<T::Wrapper<Ty<T>>>,
        mutable: bool,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    // A parameter type
    Param(LocalId),

    Ext(T::Wrapper<T::ExtTy>),
}

#[macros::ast_derives]
pub struct Ty<T: AstTypes = ()> {
    ty: TyKind<T>,
}

/// Extra information attached to syntax nodes.
#[macros::ast_derives]
pub struct Metadata<T: AstTypes = ()> {
    /// The location in the source code.
    pub span: Span,
    /// Rust attributes.
    pub attrs: Attributes<T>,
    // TODO: add phase/desugar informations
}

/// A typed expression with metadata.
#[macros::ast_derives]
pub struct Expr<T: AstTypes = ()> {
    /// The kind of expression.
    pub kind: Box<ExprKind<T>>,
    /// The type of this expression.
    pub ty: T::Wrapper<Ty<T>>,
    /// Source span and attributes.
    pub meta: T::Wrapper<Metadata<T>>,
}

/// A typed pattern with metadata.
#[macros::ast_derives]
pub struct Pat<T: AstTypes = ()> {
    /// The kind of pattern.
    pub kind: Box<PatKind<T>>,
    /// The type of this pattern.
    pub ty: T::Wrapper<Ty<T>>,
    /// Source span and attributes.
    pub meta: T::Wrapper<Metadata<T>>,
}

/// A pattern matching arm with metadata.
#[macros::ast_derives]
pub struct Arm<T: AstTypes = ()> {
    /// The pattern of the arm.
    pub pat: T::Wrapper<Pat<T>>,
    /// The body of the arm.
    pub body: T::Wrapper<Expr<T>>,
    /// The optional guard of the arm.
    pub guard: Option<T::Wrapper<Guard<T>>>,
    /// Source span and attributes.
    pub meta: T::Wrapper<Metadata<T>>,
}

/// A pattern matching arm guard with metadata.
#[macros::ast_derives]
pub struct Guard<T: AstTypes = ()> {
    /// The kind of guard.
    pub kind: T::Wrapper<GuardKind<T>>,
    /// Source span and attributes.
    pub meta: T::Wrapper<Metadata<T>>,
}

/// Represents different levels of borrowing.
#[macros::ast_derives]
pub enum BorrowKind {
    /// Shared reference: `&x`
    Shared,
    /// Unique reference: this is internal to rustc
    Unique,
    /// Mutable reference: `&mut x`
    Mut,
}

/// Binding modes used in patterns.
#[macros::ast_derives]
pub enum BindingMode<T: AstTypes = ()> {
    /// Binding by value: `x`
    ByValue,
    /// Binding by reference: `ref x`, `ref mut x`
    ByRef(T::Wrapper<BorrowKind>),
}

/// Represents the various kinds of patterns.
#[macros::ast_derives]
pub enum PatKind<T: AstTypes = ()> {
    /// Wildcard pattern: `_`
    Wild,

    /// A variable binding.
    /// Examples:
    /// - `x` → `mutable: false`
    /// - `mut x` → `mutable: true`
    /// - `ref x` → `mode: ByRef(Shared)`
    Binding {
        mutable: bool,
        var: LocalId,
        mode: T::Wrapper<BindingMode<T>>,
    },

    /// A constructor pattern
    Construct {
        constructor: GlobalId,
        is_record: bool,
        is_struct: bool,
        fields: Vec<(GlobalId, T::Wrapper<Pat<T>>)>,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    Ext(T::Wrapper<T::ExtPat>),
}

/// Represents the various kinds of pattern guards.
#[macros::ast_derives]
pub enum GuardKind<T: AstTypes = ()> {
    /// An `if let` guard
    IfLet {
        lhs: T::Wrapper<Pat<T>>,
        rhs: T::Wrapper<Expr<T>>,
    },
}

#[macros::ast_derives]
pub struct ImplExpr<T: AstTypes>(PhantomData<T>);

/// Describes the shape of an expression.
// TODO: Kill some nodes (e.g. `Array`, `Tuple`)?
#[macros::ast_derives]
pub enum ExprKind<T: AstTypes = ()> {
    /// If expression.
    /// Example: `if x > 0 { 1 } else { 2 }`
    If {
        condition: T::Wrapper<Expr<T>>,
        then: T::Wrapper<Expr<T>>,
        else_: Option<T::Wrapper<Expr<T>>>,
    },

    /// Function application.
    /// Example: `f(x, y)`
    App {
        head: T::Wrapper<Expr<T>>,
        args: Vec<T::Wrapper<Expr<T>>>,
        generic_args: Vec<T::Wrapper<GenericValue<T>>>,
        bounds_impls: Vec<T::Wrapper<ImplExpr<T>>>,
        trait_: Option<(T::Wrapper<ImplExpr<T>>, Vec<T::Wrapper<GenericValue<T>>>)>,
    },

    /// A literal value.
    /// Example: `42`, `"hello"`
    Literal(Literal),

    /// An array literal.
    /// Example: `[1, 2, 3]`
    Array(Vec<T::Wrapper<Expr<T>>>),

    /// A constructor application
    /// Example: A(x)
    Construct {
        constructor: GlobalId,
        is_record: bool,
        is_struct: bool,
        fields: Vec<(GlobalId, T::Wrapper<Expr<T>>)>,
        base: Option<T::Wrapper<Expr<T>>>,
    },

    Match {
        scrutinee: T::Wrapper<Expr<T>>,
        arms: Vec<T::Wrapper<Arm<T>>>,
    },

    /// A tuple literal.
    /// Example: `(a, b)`
    Tuple(Vec<T::Wrapper<Expr<T>>>),

    /// A reference expression.
    /// Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow {
        mutable: bool,
        inner: T::Wrapper<Expr<T>>,
    },

    /// A dereference: `*x`
    Deref(T::Wrapper<Expr<T>>),

    /// A `let` expression used in expressions.
    /// Example: `let x = 1; x + 1`
    Let {
        lhs: T::Wrapper<Pat<T>>,
        rhs: T::Wrapper<Expr<T>>,
        body: T::Wrapper<Expr<T>>,
    },

    /// A global identifier.
    /// Example: `std::mem::drop`
    GlobalId(GlobalId),

    /// A local variable.
    /// Example: `x`
    LocalId(LocalId),

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    /// Type ascription
    Ascription {
        e: T::Wrapper<Expr<T>>,
        ty: T::Wrapper<Ty<T>>,
    },

    /// Variable mutation
    /// Example: `x = 1`
    Assign {
        lhs: T::Wrapper<Expr<T>>,
        value: T::Wrapper<Expr<T>>,
    },

    /// Loop
    /// Example: `loop{}`
    Loop {
        body: T::Wrapper<Expr<T>>,
        label: Option<String>,
    },

    /// Break out of a loop
    /// Example: `break`
    Break {
        value: T::Wrapper<Expr<T>>,
        label: Option<String>,
    },

    /// Return from a function
    /// Example: `return 1`
    Return {
        value: T::Wrapper<Expr<T>>,
    },

    /// Continue (go to next loop iteration)
    /// Example: `continue`
    Continue {
        label: Option<String>,
    },

    /// Closure (anonymous function)
    /// Example: `|x| x`
    Closure {
        params: Vec<T::Wrapper<Pat<T>>>,
        body: T::Wrapper<Expr<T>>,
        captures: Vec<T::Wrapper<Expr<T>>>,
    },

    Ext(T::Wrapper<T::ExtExpr>),
}

/// Represents the kinds of generic parameters
#[macros::ast_derives]
pub enum GenericParamKind<T: AstTypes = ()> {
    Lifetime,
    Type,
    Const { ty: T::Wrapper<Ty<T>> },
}

/// Represents an instantiated trait that needs to be implemented
#[macros::ast_derives]
pub struct TraitGoal<T: AstTypes = ()> {
    trait_: GlobalId,
    args: Vec<T::Wrapper<GenericValue<T>>>,
}

/// Represents a trait bound in a generic constraint
#[macros::ast_derives]
pub struct ImplIdent<T: AstTypes = ()> {
    goal: T::Wrapper<TraitGoal<T>>,
    name: String,
}

#[macros::ast_derives]
pub struct ProjectionPredicate<T>(PhantomData<T>);

/// A generic constraint (lifetime, type or projection)
#[macros::ast_derives]
pub enum GenericConstraint<T: AstTypes = ()> {
    Lifetime(String),
    Type(T::Wrapper<ImplIdent<T>>),
    Projection(T::Wrapper<ProjectionPredicate<T>>),
}

/// A generic parameter (lifetime, type parameter or const parameter)
#[macros::ast_derives]
pub struct GenericParam<T: AstTypes = ()> {
    pub ident: LocalId,
    pub meta: T::Wrapper<Metadata<T>>,
    pub kind: T::Wrapper<GenericParamKind<T>>,
}

/// Generic parameters and constraints (contained between `<>` in function declarations)
#[macros::ast_derives]
pub struct Generics<T: AstTypes = ()> {
    pub params: Vec<T::Wrapper<GenericParam<T>>>,
    pub constraints: Vec<T::Wrapper<GenericConstraint<T>>>,
}

/// Safety level of a function.
#[macros::ast_derives]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}

/// Represents a single attribute.
// TODO: implement
#[macros::ast_derives]
pub struct Attribute<T: AstTypes = ()>(PhantomData<T>);

/// A list of attributes.
pub type Attributes<T> = Vec<Attribute<T>>;

/// A type with its associated span.
#[macros::ast_derives]
pub struct SpannedTy<T: AstTypes = ()> {
    pub span: Span,
    pub ty: T::Wrapper<Ty<T>>,
}

/// A function parameter (pattern + type, e.g. `x: u8`).
#[macros::ast_derives]
pub struct Param<T: AstTypes = ()> {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: T::Wrapper<Pat<T>>,
    /// Type part with span.
    pub ty: T::Wrapper<SpannedTy<T>>,
    /// Attributes
    pub attributes: Attributes<T>,
}

/// A top-level item in the module.
#[macros::ast_derives]
pub enum ItemKind<T: AstTypes = ()> {
    /// A function or constant item.
    /// Example:
    /// ```rust
    /// fn add<T: Clone>(x: i32, y: i32) -> i32 {
    ///     x + y
    /// }
    /// ```
    /// Constants are represented as functions of arity zero, while functions always have a non-zero arity.
    Fn {
        /// The identifier of the function.
        /// Example: `add`
        name: GlobalId,
        /// The generic arguments and constraints of the function.
        /// Example: the generic type `T` and the constraint `T: Clone`
        generics: T::Wrapper<Generics<T>>,
        /// The body of the function
        /// Example: `x + y`
        body: T::Wrapper<Expr<T>>,
        /// The parameters of the function.
        /// Example: `x: i32, y: i32`
        params: Vec<T::Wrapper<Param<T>>>,
        /// The safety of the function.
        safety: T::Wrapper<SafetyKind>,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// A top-level item with metadata.
#[macros::ast_derives]
pub struct Item<T: AstTypes = ()> {
    /// The global identifier of the item.
    pub ident: GlobalId,
    /// The kind of the item.
    pub kind: ItemKind<T>,
    /// Source span and attributes.
    pub meta: T::Wrapper<Metadata<T>>,
}

// pub mod traits {
//     use super::*;
//     pub trait HasMetadata {
//         fn metadata(&self) -> &Metadata;
//     }
//     pub trait HasSpan {
//         fn span(&self) -> Span;
//     }
//     pub trait Typed {
//         fn ty(&self) -> &Ty;
//     }
//     impl<T: HasMetadata> HasSpan for T {
//         fn span(&self) -> Span {
//             self.metadata().span
//         }
//     }
//     pub trait HasKind {
//         type Kind;
//         fn kind(&self) -> &Self::Kind;
//     }

//     macro_rules! derive_has_metadata {
//         ($($ty:ty),*) => {
//             $(impl HasMetadata for $ty {
//                 fn metadata(&self) -> &Metadata {
//                     &self.meta
//                 }
//             })*
//         };
//     }
//     macro_rules! derive_has_kind {
//         ($($ty:ty => $kind:ty),*) => {
//             $(impl HasKind for $ty {
//                 type Kind = $kind;
//                 fn kind(&self) -> &Self::Kind {
//                     &self.kind
//                 }
//             })*
//         };
//     }

//     derive_has_metadata!(Item, Expr, Pat);
//     derive_has_kind!(Item => ItemKind, Expr => ExprKind, Pat => PatKind);

//     impl Typed for Expr {
//         fn ty(&self) -> &Ty {
//             &self.ty
//         }
//     }
//     impl Typed for Pat {
//         fn ty(&self) -> &Ty {
//             &self.ty
//         }
//     }
//     impl Typed for SpannedTy {
//         fn ty(&self) -> &Ty {
//             &self.ty
//         }
//     }

//     impl HasSpan for SpannedTy {
//         fn span(&self) -> Span {
//             self.span
//         }
//     }

//     impl ExprKind {
//         pub fn into_expr(self, span: Span, ty: Ty, attrs: Vec<Attribute>) -> Expr {
//             Expr {
//                 kind: Box::new(self),
//                 ty,
//                 meta: Metadata { span, attrs },
//             }
//         }
//     }
// }
// pub use traits::*;
//
