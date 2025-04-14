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
pub mod helper;
pub mod identifiers;
pub mod literals;
pub mod node;
pub mod span;

pub use diagnostics::Diagnostic;
pub use identifiers::*;
pub use literals::*;
pub use node::Node;
pub use span::Span;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum GenericValue {
    /// A type-level generic value.
    /// Example: `i32` in `Vec<i32>`
    Ty(Ty),
    /// A const-level generic value.
    /// Example: `12` in `Foo<12>`
    Expr(Expr),
    /// A lifetime.
    /// Example: `'a` in `foo<'a>`
    Lifetime,
}

/// Built-in primitive types.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum PrimitiveTy {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(IntKind),
}

/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum Ty {
    /// A primitive type.
    /// Example: `i32`, `bool`
    Primitive(PrimitiveTy),

    /// A tuple type.
    /// Example: `(i32, bool)`
    Tuple(Vec<Ty>),

    /// A type application (generic type).
    /// Example: `Vec<i32>`
    App {
        head: GlobalId,
        args: Vec<GenericValue>,
    },

    /// A function or closure type.
    /// Example: `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow {
        inputs: Vec<Ty>,
        output: Box<Ty>,
    },

    /// A reference type.
    /// Example: `&i32`, `&mut i32`
    Ref {
        inner: Box<Ty>,
        mutable: bool,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    // A parameter type
    Param(LocalId),
}

/// Extra information attached to syntax nodes.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Metadata {
    /// The location in the source code.
    pub span: Span,
    /// Rust attributes.
    pub attrs: Attributes,
    // TODO: add phase/desugar informations
}

/// A typed expression with metadata.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Expr {
    /// The kind of expression.
    pub kind: Box<ExprKind>,
    /// The type of this expression.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A typed pattern with metadata.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Pat {
    /// The kind of pattern.
    pub kind: Box<PatKind>,
    /// The type of this pattern.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A pattern matching arm with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Arm {
    /// The pattern of the arm.
    pub pat: Pat,
    /// The body of the arm.
    pub body: Expr,
    /// The optional guard of the arm.
    pub guard: Option<Guard>,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A pattern matching arm guard with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Guard {
    /// The kind of guard.
    pub kind: GuardKind,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// Represents different levels of borrowing.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum BorrowKind {
    /// Shared reference: `&x`
    Shared,
    /// Unique reference: this is internal to rustc
    Unique,
    /// Mutable reference: `&mut x`
    Mut,
}

/// Binding modes used in patterns.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum BindingMode {
    /// Binding by value: `x`
    ByValue,
    /// Binding by reference: `ref x`, `ref mut x`
    ByRef(BorrowKind),
}

/// Represents the various kinds of patterns.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum PatKind {
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
        mode: BindingMode,
    },

    /// A constructor pattern
    Construct {
        constructor: GlobalId,
        is_record: bool,
        is_struct: bool,
        fields: Vec<(GlobalId, Pat)>,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// Represents the various kinds of pattern guards.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GuardKind {
    /// An `if let` guard
    IfLet { lhs: Pat, rhs: Expr },
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplExpr;

/// Describes the shape of an expression.
// TODO: Kill some nodes (e.g. `Array`, `Tuple`)?
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum ExprKind {
    /// If expression.
    /// Example: `if x > 0 { 1 } else { 2 }`
    If {
        condition: Expr,
        then: Expr,
        else_: Option<Expr>,
    },

    /// Function application.
    /// Example: `f(x, y)`
    App {
        head: Expr,
        args: Vec<Expr>,
        generic_args: Vec<GenericValue>,
        bounds_impls: Vec<ImplExpr>,
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
    },

    /// A literal value.
    /// Example: `42`, `"hello"`
    Literal(Literal),

    /// An array literal.
    /// Example: `[1, 2, 3]`
    Array(Vec<Expr>),

    /// A constructor application
    /// Example: A(x)
    Construct {
        constructor: GlobalId,
        is_record: bool,
        is_struct: bool,
        fields: Vec<(GlobalId, Expr)>,
        base: Option<Expr>,
    },

    Match {
        scrutinee: Expr,
        arms: Vec<Arm>,
    },

    /// A tuple literal.
    /// Example: `(a, b)`
    Tuple(Vec<Expr>),

    /// A reference expression.
    /// Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow {
        mutable: bool,
        inner: Expr,
    },

    /// A dereference: `*x`
    Deref(Expr),

    /// A `let` expression used in expressions.
    /// Example: `let x = 1; x + 1`
    Let {
        lhs: Pat,
        rhs: Expr,
        body: Expr,
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
        e: Expr,
        ty: Ty,
    },

    /// Variable mutation
    /// Example: `x = 1`
    Assign {
        lhs: Expr,
        value: Expr,
    },

    /// Loop
    /// Example: `loop{}`
    Loop {
        body: Expr,
        label: Option<String>,
    },

    /// Break out of a loop
    /// Example: `break`
    Break {
        value: Expr,
        label: Option<String>,
    },

    /// Return from a function
    /// Example: `return 1`
    Return {
        value: Expr,
    },

    /// Continue (go to next loop iteration)
    /// Example: `continue`
    Continue {
        label: Option<String>,
    },

    /// Closure (anonymous function)
    /// Example: `|x| x`
    Closure {
        params: Vec<Pat>,
        body: Expr,
        captures: Vec<Expr>,
    },
}

/// Represents the kinds of generic parameters
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericParamKind {
    Lifetime,
    Type,
    Const { ty: Ty },
}

/// Represents an instantiated trait that needs to be implemented
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct TraitGoal {
    pub trait_: GlobalId,
    pub args: Vec<GenericValue>,
}

/// Represents a trait bound in a generic constraint
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplIdent {
    pub goal: TraitGoal,
    pub name: String,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProjectionPredicate;

/// A generic constraint (lifetime, type or projection)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericConstraint {
    Lifetime(String),
    Type(ImplIdent),
    Projection(ProjectionPredicate),
}

/// A generic parameter (lifetime, type parameter or const parameter)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct GenericParam {
    pub ident: LocalId,
    pub meta: Metadata,
    pub kind: GenericParamKind,
}

/// Generic parameters and constraints (contained between `<>` in function declarations)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub constraints: Vec<GenericConstraint>,
}

/// Safety level of a function.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}

/// Represents a single attribute.
// TODO: implement
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Attribute;

/// A list of attributes.
pub type Attributes = Vec<Attribute>;

/// A type with its associated span.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct SpannedTy {
    pub span: Span,
    pub ty: Ty,
}

/// A function parameter (pattern + type, e.g. `x: u8`).
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Param {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: Pat,
    /// Type part with span.
    pub ty: SpannedTy,
    /// Attributes
    pub attributes: Attributes,
}

/// A top-level item in the module.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub enum ItemKind {
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
        generics: Generics,
        /// The body of the function
        /// Example: `x + y`
        body: Expr,
        /// The parameters of the function.
        /// Example: `x: i32, y: i32`
        params: Vec<Param>,
        /// The safety of the function.
        safety: SafetyKind,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// A top-level item with metadata.
#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct Item {
    /// The global identifier of the item.
    pub ident: GlobalId,
    /// The kind of the item.
    pub kind: ItemKind,
    /// Source span and attributes.
    pub meta: Metadata,
}

pub mod traits {
    use super::*;
    pub trait HasMetadata {
        fn metadata(&self) -> &Metadata;
    }
    pub trait HasSpan {
        fn span(&self) -> Span;
    }
    pub trait Typed {
        fn ty(&self) -> &Ty;
    }
    impl<T: HasMetadata> HasSpan for T {
        fn span(&self) -> Span {
            self.metadata().span
        }
    }
    pub trait HasKind {
        type Kind;
        fn kind(&self) -> &Self::Kind;
    }

    macro_rules! derive_has_metadata {
        ($($ty:ty),*) => {
            $(impl HasMetadata for $ty {
                fn metadata(&self) -> &Metadata {
                    &self.meta
                }
            })*
        };
    }
    macro_rules! derive_has_kind {
        ($($ty:ty => $kind:ty),*) => {
            $(impl HasKind for $ty {
                type Kind = $kind;
                fn kind(&self) -> &Self::Kind {
                    &self.kind
                }
            })*
        };
    }

    derive_has_metadata!(Item, Expr, Pat);
    derive_has_kind!(Item => ItemKind, Expr => ExprKind, Pat => PatKind);

    impl Typed for Expr {
        fn ty(&self) -> &Ty {
            &self.ty
        }
    }
    impl Typed for Pat {
        fn ty(&self) -> &Ty {
            &self.ty
        }
    }
    impl Typed for SpannedTy {
        fn ty(&self) -> &Ty {
            &self.ty
        }
    }

    impl HasSpan for SpannedTy {
        fn span(&self) -> Span {
            self.span
        }
    }

    impl ExprKind {
        pub fn into_expr(self, span: Span, ty: Ty, attrs: Vec<Attribute>) -> Expr {
            Expr {
                kind: Box::new(self),
                ty,
                meta: Metadata { span, attrs },
            }
        }
    }
}
pub use traits::*;
