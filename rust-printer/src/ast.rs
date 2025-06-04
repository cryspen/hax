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

pub mod derives;
pub mod diagnostics;
pub mod helper;
pub mod identifiers;
pub mod literals;
pub mod node;
pub mod span;

pub use derives::*;
pub use diagnostics::Diagnostic;
use hax_frontend_exporter::Mutability;
pub use identifiers::*;
pub use literals::*;
pub use node::Node;
pub use span::Span;

/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[apply(derive_AST)]
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
#[apply(derive_AST)]
pub enum PrimitiveTy {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(IntKind),
    /// A float type (e.g. `f32`)
    Float(FloatKind),
    /// The `char` type
    Char,
    /// The `str` type
    Str,
}

/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[apply(derive_AST)]
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

    /// A parameter type
    Param(LocalId),

    /// A slice type.
    /// Example `&[i32]`
    Slice(Box<Ty>),

    /// An array type.
    /// Example `&[i32; 10]`
    Array { ty: Box<Ty>, length: Box<Expr> },

    /// A raw pointer type
    RawPointer,

    /// An associated type
    AssociatedType { impl_: ImplExpr, item: GlobalId },

    /// An opaque type
    Opaque(GlobalId),

    /// A dyn type
    Dyn(Vec<DynTraitGoal>),
}

/// A dyn trait. The generic arguments are known but the actual type
/// implementing the trait is known dynamically.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct DynTraitGoal {
    trait_: GlobalId,
    non_self_args: Vec<GenericValue>,
}

/// Extra information attached to syntax nodes.
#[apply(derive_AST)]
pub struct Metadata {
    /// The location in the source code.
    pub span: Span,
    /// Rust attributes.
    pub attributes: Attributes,
    // TODO: add phase/desugar informations
}

/// A typed expression with metadata.
#[apply(derive_AST)]
pub struct Expr {
    /// The kind of expression.
    pub kind: Box<ExprKind>,
    /// The type of this expression.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A typed pattern with metadata.
#[apply(derive_AST)]
pub struct Pat {
    /// The kind of pattern.
    pub kind: Box<PatKind>,
    /// The type of this pattern.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A pattern matching arm with metadata.
#[apply(derive_AST)]
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
#[apply(derive_AST)]
pub struct Guard {
    /// The kind of guard.
    pub kind: GuardKind,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// Represents different levels of borrowing.
#[apply(derive_AST)]
pub enum BorrowKind {
    /// Shared reference: `&x`
    Shared,
    /// Unique reference: this is internal to rustc
    Unique,
    /// Mutable reference: `&mut x`
    Mut,
}

/// Binding modes used in patterns.
#[apply(derive_AST)]
pub enum BindingMode {
    /// Binding by value: `x`
    ByValue,
    /// Binding by reference: `ref x`, `ref mut x`
    ByRef(BorrowKind),
}

/// Represents the various kinds of patterns.
#[apply(derive_AST)]
pub enum PatKind {
    /// Wildcard pattern: `_`
    Wild,

    /// An ascription pattern: p : ty
    Ascription { ty: Ty, typ_span: Span, pat: Pat },

    /// An or pattern: p | q
    /// Always contains at least 2 sub-patterns
    Or { subpats: Vec<Pat> },

    /// An array pattern: [p, q]
    Array { args: Vec<Pat> },

    /// A dereference pattern: &p
    Deref { subpat: Pat },

    /// A constant pattern: 1
    Constant { lit: Literal },

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
#[apply(derive_AST)]
pub enum GuardKind {
    /// An `if let` guard
    IfLet { lhs: Pat, rhs: Expr },
}

/// The left-hand side of an assignment.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Lhs {
    LocalVar {
        var: LocalId,
        ty: Ty,
    },
    ArbitraryExpr(Box<Expr>),
    FieldAccessor {
        e: Box<Lhs>,
        ty: Ty,
        field: GlobalId,
    },
    ArrayAccessor {
        e: Box<Lhs>,
        ty: Ty,
        index: Expr,
    },
}

/// Represents a witness of trait implementation
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplExpr {
    kind: Box<ImplExprKind>,
    goal: TraitGoal,
}

/// Represents all the kinds of impl expr
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ImplExprKind {
    Self_,
    Concrete(TraitGoal),
    LocalBound {
        id: String,
    },
    Parent {
        impl_: ImplExpr,
        item: GlobalId,
    },
    Projection {
        impl_: ImplExpr,
        item: GlobalId,
        ident: ImplIdent,
    },
    ImplApp {
        impl_: ImplExpr,
        args: Vec<ImplExpr>,
    },
    Dyn,
    Builtin(TraitGoal),
}

/// Represents an impl item (associated type or fn)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplItem {
    meta: Metadata,
    generics: Generics,
    kind: ImplItemKind,
    ident: GlobalId,
}

/// Represents the kinds of impl items
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
enum ImplItemKind {
    Type {
        ty: Ty,
        parent_bounds: Vec<(ImplExpr, ImplIdent)>,
    },
    Fn {
        body: Expr,
        params: Vec<Param>,
    },
}

/// Represents a trait item (associated type, fn, or default)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct TraitItem {
    kind: TraitItemKind,
    generics: Generics,
    ident: GlobalId,
    meta: Metadata,
}

/// Represents the kinds of trait items
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum TraitItemKind {
    Type(Vec<ImplIdent>),
    Fn(Ty),
    Default { params: Vec<Param>, body: Expr },
}

// Represents an inlined piece of backend code
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum QuoteContent {
    Verbatim(String),
    Expr(Expr),
    Pattern(Pat),
    Typ(Ty),
}

pub type Quote = Vec<QuoteContent>;

/// The origin of a quote item
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ItemQuoteOrigin {
    item_kind: Box<ItemKind>,
    item_ident: GlobalId,
    position: ItemQuoteOriginPosition,
}

/// The position of a quote item relative to its origin
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ItemQuoteOriginPosition {
    Before,
    After,
    Replace,
}

/// The kind of a loop (resugared).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum LoopKind {
    UnconditionalLoop,
    WhileLoop {
        condition: Expr,
    },
    ForLoop {
        pat: Pat,
        it: Expr,
    },
    ForIndexLoop {
        start: Expr,
        end: Expr,
        var: LocalId,
        var_typ: Ty,
    },
}

/// This is a marker to describe what control flow is present in a loop.
/// It is added by phase `DropReturnBreakContinue` and the information is used in
/// `FunctionalizeLoops`. We need it to replace the control flow nodes of the AST
/// by an encoding in the `ControlFlow` enum.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ControlFlowKind {
    BreakOnly,
    BreakOrReturn,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct LoopState {
    init: Expr,
    bpat: Pat,
}

/// Describes the shape of an expression.
// TODO: Kill some nodes (e.g. `Array`, `Tuple`)?
#[apply(derive_AST)]
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

    /// Raw borrow
    AddressOf {
        mutability: Mutability,
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
        lhs: Lhs,
        value: Expr,
    },

    /// Loop
    /// Example: `loop{}`
    Loop {
        body: Expr,
        kind: LoopKind,
        state: Option<LoopState>,
        contrl_flow: Option<ControlFlowKind>,
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

    /// A quote is an inlined piece of backend code
    Quote {
        contents: Quote,
    },
}

/// Represents the kinds of generic parameters
#[apply(derive_AST)]
pub enum GenericParamKind {
    Lifetime,
    Type,
    Const { ty: Ty },
}

/// Represents an instantiated trait that needs to be implemented
#[apply(derive_AST)]
pub struct TraitGoal {
    pub trait_: GlobalId,
    pub args: Vec<GenericValue>,
}

/// Represents a trait bound in a generic constraint
#[apply(derive_AST)]
pub struct ImplIdent {
    pub goal: TraitGoal,
    pub name: String,
}

/// A projection predicate expresses a constraint over an associated type:
/// ```rust
/// fn f<T: Foo<S = String>>(...)
/// ```
/// In this example `Foo` has an associated type `S`.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProjectionPredicate {
    impl_: ImplExpr,
    assoc_item: GlobalId,
    ty: Ty,
}

/// A generic constraint (lifetime, type or projection)
#[apply(derive_AST)]
pub enum GenericConstraint {
    Lifetime(String),
    Type(ImplIdent),
    Projection(ProjectionPredicate),
}

/// A generic parameter (lifetime, type parameter or const parameter)
#[apply(derive_AST)]
pub struct GenericParam {
    pub ident: LocalId,
    pub meta: Metadata,
    pub kind: GenericParamKind,
}

/// Generic parameters and constraints (contained between `<>` in function declarations)
#[apply(derive_AST)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub constraints: Vec<GenericConstraint>,
}

/// Safety level of a function.
#[apply(derive_AST)]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}

/// Represents a single attribute.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Attribute {
    kind: AttributeKind,
    span: Span,
}

/// Represents the kind of an attribute.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum AttributeKind {
    Tool { path: String, tokens: String },
    DocComment { kind: DocCommentKind, body: String },
}

/// Represents the kind of a doc comment.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum DocCommentKind {
    Line,
    Block,
}

/// A list of attributes.
pub type Attributes = Vec<Attribute>;

/// A type with its associated span.
#[apply(derive_AST)]
pub struct SpannedTy {
    pub span: Span,
    pub ty: Ty,
}

/// A function parameter (pattern + type, e.g. `x: u8`).
#[apply(derive_AST)]
pub struct Param {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: Pat,
    /// Type part with span.
    pub ty: SpannedTy,
    /// Attributes
    pub attributes: Attributes,
}

/// A variant of an enum or struct.
/// In our representation structs always have one variant with an argument for each field.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Variant {
    name: GlobalId,
    arguments: Vec<(GlobalId, Ty, Attributes)>,
    is_record: bool,
    attributes: Attributes,
}

/// A top-level item in the module.
#[apply(derive_AST)]
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

    /// A type alias.
    /// Example:
    /// ```rust
    /// type A = u8;
    /// ```
    TyAlias {
        name: GlobalId,
        generics: Generics,
        ty: Ty,
    },

    /// A type definition (struct or enum)
    /// Example:
    /// ```rust
    /// enum A {B, C}
    /// struct S {f: u8}
    /// ```
    Type {
        name: GlobalId,
        generics: Generics,
        variants: Vec<Variant>,
        is_struct: bool,
    },

    /// A trait definition. Example:
    /// ```rust
    /// trait T<A> {
    ///     type Assoc;
    ///     fn m(x: Self::Assoc, y: Self) -> A;
    /// }
    /// ```
    Trait {
        name: GlobalId,
        generics: Generics,
        items: Vec<TraitItem>,
    },

    /// A trait implementation. Example:
    /// ```rust
    /// impl T<u8> for u16 {
    ///     type Assoc = u32;
    ///     fn m(x: u32, y: u16) -> u8 {
    ///         (x as u8) + (y as u8)
    ///     }
    /// }
    /// ```
    Impl {
        generics: Generics,
        self_ty: Ty,
        of_trait: Vec<(GlobalId, GenericValue)>,
        items: Vec<ImplItem>,
        parent_bounds: Vec<(ImplExpr, ImplIdent)>,
        safety: SafetyKind,
    },

    /// ` use item as name; `
    Alias {
        name: GlobalId,
        item: GlobalId,
    },

    /// A `use` statement
    Use {
        path: Vec<String>,
        is_external: bool,
        rename: Option<String>,
    },

    /// A `Quote` node is inserted by phase TransformHaxLibInline to deal with some `hax_lib` features.
    /// For example insertion of verbatim backend code.
    Quote {
        quote: Quote,
        origin: ItemQuoteOrigin,
    },

    IMacroInvocation {
        macro_name: GlobalId,
        argument: String,
        spam: Span,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    NotImplementedYet,
}

/// A top-level item with metadata.
#[apply(derive_AST)]
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
        pub fn into_expr(self, span: Span, ty: Ty, attributes: Vec<Attribute>) -> Expr {
            Expr {
                kind: Box::new(self),
                ty,
                meta: Metadata { span, attributes },
            }
        }
    }
}
pub use traits::*;
