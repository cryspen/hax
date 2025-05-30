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
pub mod identifiers;
pub mod literals;
pub mod node;
pub mod span;

pub use diagnostics::Diagnostic;
pub use identifiers::*;
pub use literals::*;
pub use node::Node;
pub use span::Span;

/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericValue {
    /// A type-level generic value.
    /// Example: `i32` in `Vec<i32>`
    Ty(Ty),
    /// A const-level generic value.
    /// Example: `12` in `Foo<12>`
    Expr(Expr),
}

/// Built-in primitive types.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PrimitiveTy {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(IntKind),
}

/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
    Arrow { inputs: Vec<Ty>, output: Box<Ty> },

    /// A reference type.
    /// Example: `&i32`, `&mut i32`
    Ref { inner: Box<Ty>, mutable: bool },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// Extra information attached to syntax nodes.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Metadata {
    /// The location in the source code.
    pub span: Span,
    /// Rust attributes.
    pub attrs: Attributes,
    // TODO: add phase/desugar informations
}

/// A typed expression with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Expr {
    /// The kind of expression.
    pub kind: Box<ExprKind>,
    /// The type of this expression.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A typed pattern with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Pat {
    /// The kind of pattern.
    pub kind: PatKind,
    /// The type of this pattern.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// Represents different levels of borrowing.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum BorrowKind {
    /// Shared reference: `&x`
    Shared,
    /// Unique reference: this is internal to rustc
    Unique,
    /// Mutable reference: `&mut x`
    Mut,
}

/// Binding modes used in patterns.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum BindingMode {
    /// Binding by value: `x`
    ByValue,
    /// Binding by reference: `ref x`, `ref mut x`
    ByRef(BorrowKind),
}

/// Represents the various kinds of patterns.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// Describes the shape of an expression.
// TODO: Kill some nodes (e.g. `Array`, `Tuple`)?
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ExprKind {
    /// If expression.
    /// Example: `if x > 0 { 1 } else { 2 }`
    If {
        condition: Expr,
        then_: Expr,
        else_: Option<Expr>,
    },

    /// Function application.
    /// Example: `f(x, y)`
    // TODO: generics, traits
    App { head: Expr, args: Vec<Expr> },

    /// A literal value.
    /// Example: `42`, `"hello"`
    Literal(Literal),

    /// An array literal.
    /// Example: `[1, 2, 3]`
    Array(Vec<Expr>),

    /// A tuple literal.
    /// Example: `(a, b)`
    Tuple(Vec<Expr>),

    /// A reference expression.
    /// Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow { mutable: bool, inner: Expr },

    /// A dereference: `*x`
    Deref(Expr),

    /// A `let` expression used in expressions.
    /// Example: `let x = 1; x + 1`
    Let { lhs: Pat, rhs: Expr, body: Expr },

    /// A global identifier.
    /// Example: `std::mem::drop`
    GlobalId(GlobalId),

    /// A local variable.
    /// Example: `x`
    LocalId(LocalId),

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

// TODO: implement generics
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Generics;

/// Safety level of a function.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}

/// Represents a single attribute.
// TODO: implement
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Attribute;

/// A list of attributes.
pub type Attributes = Vec<Attribute>;

/// A type with its associated span.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct SpannedTy {
    pub span: Span,
    pub ty: Ty,
}

/// A function parameter (pattern + type, e.g. `x: u8`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Param {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: Pat,
    /// Type part with span.
    pub ty: SpannedTy,
    /// Attributes
    pub attributes: Attributes,
}

/// A top-level item in the module.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
