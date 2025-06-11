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
pub mod fragment;
pub mod identifiers;
pub mod literals;
pub mod span;

use crate::symbol::Symbol;
pub use diagnostics::Diagnostic;
pub use fragment::Fragment;
use hax_frontend_exporter::Mutability;
pub use hax_rust_engine_macros::*;
pub use identifiers::*;
pub use literals::*;
pub use span::Span;

/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[derive_group_for_ast]
pub enum GenericValue {
    /// A type-level generic value.
    ///
    /// # Example:
    /// `i32` in `Vec<i32>`
    Ty(Ty),
    /// A const-level generic value.
    ///
    /// # Example:
    /// `12` in `Foo<12>`
    Expr(Expr),
    /// A lifetime.
    ///
    /// # Example:
    /// `'a` in `foo<'a>`
    Lifetime,
}

/// Built-in primitive types.
#[derive_group_for_ast]
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
#[derive_group_for_ast]
pub struct Region;

pub type Ty = Box<TyKind>;

/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[derive_group_for_ast]
pub enum TyKind {
    /// A primitive type.
    ///
    /// # Example:
    /// `i32`, `bool`
    Primitive(PrimitiveTy),

    /// A tuple type.
    ///
    /// # Example:
    /// `(i32, bool)`
    Tuple(Vec<Ty>),

    /// A type application (generic type).
    ///
    /// # Example:
    /// `Vec<i32>`
    App {
        head: GlobalId,
        args: Vec<GenericValue>,
    },

    /// A function or closure type.
    ///
    /// # Example:
    /// `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow { inputs: Vec<Ty>, output: Ty },

    // TODO: Should we keep this type?
    /// A reference type.
    ///
    /// # Example:
    /// `&i32`, `&mut i32`
    Ref {
        inner: Ty,
        mutable: bool,
        region: Region,
    },

    /// A parameter type
    Param(LocalId),

    // TODO: Should we keep this type?
    /// A slice type.
    ///
    /// # Example:
    /// `&[i32]`
    Slice(Ty),

    /// An array type.
    ///
    /// # Example:
    /// `&[i32; 10]`
    Array { ty: Ty, length: Box<Expr> },

    /// A raw pointer type
    RawPointer,

    /// An associated type
    ///
    /// # Example:
    /// ```rust
    ///     fn f<T: Tr>() -> T::A {...}
    /// ```
    AssociatedType {
        /// Impl expr for `Tr<T>` in the example
        impl_: ImplExpr,
        /// `Tr::A` in the example
        item: GlobalId,
    },

    /// An opaque type
    ///
    /// # Example:
    /// ```rust
    /// type Foo = impl Bar;
    /// ```
    Opaque(GlobalId),

    /// A `dyn` type
    ///
    /// # Example:
    /// ```rust
    /// dyn Tr
    /// ```
    Dyn(Vec<DynTraitGoal>),

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// A `dyn` trait. The generic arguments are known but the actual type
/// implementing the trait is known dynamically.
///
/// # Example:
/// ```rust
/// dyn Tr<A, B>
/// ```
#[derive_group_for_ast]
pub struct DynTraitGoal {
    /// `Tr` in the example above
    pub trait_: GlobalId,
    /// `A, B` in the example above
    pub non_self_args: Vec<GenericValue>,
}

/// Extra information attached to syntax nodes.
#[derive_group_for_ast]
pub struct Metadata {
    /// The location in the source code.
    pub span: Span,
    /// Rust attributes.
    pub attributes: Attributes,
    // TODO: add phase/desugar informations
}

/// A typed expression with metadata.
#[derive_group_for_ast]
pub struct Expr {
    /// The kind of expression.
    pub kind: Box<ExprKind>,
    /// The type of this expression.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A typed pattern with metadata.
#[derive_group_for_ast]
pub struct Pat {
    /// The kind of pattern.
    pub kind: Box<PatKind>,
    /// The type of this pattern.
    pub ty: Ty,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// A pattern matching arm with metadata.
#[derive_group_for_ast]
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
#[derive_group_for_ast]
pub struct Guard {
    /// The kind of guard.
    pub kind: GuardKind,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// Represents different levels of borrowing.
#[derive_group_for_ast]
pub enum BorrowKind {
    /// Shared reference
    ///
    /// # Example:
    /// `&x`
    Shared,
    /// Unique reference: this is internal to rustc
    Unique,
    /// Mutable reference
    ///
    /// # Example:
    /// `&mut x`
    Mut,
}

/// Binding modes used in patterns.
#[derive_group_for_ast]
pub enum BindingMode {
    /// Binding by value
    ///
    /// # Example:
    /// `x`
    ByValue,
    /// Binding by reference
    ///
    /// # Example:
    /// `ref x`, `ref mut x`
    ByRef(BorrowKind),
}

/// Represents the various kinds of patterns.
#[derive_group_for_ast]
pub enum PatKind {
    /// Wildcard pattern
    ///
    /// # Example:
    /// `_`
    Wild,

    /// An ascription pattern
    ///
    /// # Example:
    /// `p : ty`
    Ascription { pat: Pat, ty: SpannedTy },

    /// An or pattern
    ///
    /// # Example:
    /// `p | q`
    /// Always contains at least 2 sub-patterns
    Or { sub_pats: Vec<Pat> },

    /// An array pattern
    ///
    /// # Example:
    /// `[p, q]`
    Array { args: Vec<Pat> },

    /// A dereference pattern
    ///
    /// # Example:
    /// `&p`
    Deref { sub_pat: Pat },

    /// A constant pattern
    ///
    /// # Example:
    /// `1`
    Constant { lit: Literal },

    /// A variable binding.
    ///
    /// # Examples:
    /// - `x` → `mutable: false`
    /// - `mut x` → `mutable: true`
    /// - `ref x` → `mode: ByRef(Shared)`
    Binding {
        mutable: bool,
        var: LocalId,
        mode: BindingMode,
        sub_pat: Option<Pat>,
    },

    /// A constructor pattern
    ///
    /// # Example:
    /// ```rust
    /// Foo(x)
    /// ```
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
#[derive_group_for_ast]
pub enum GuardKind {
    /// An `if let` guard
    IfLet { lhs: Pat, rhs: Expr },
}

// TODO: Replace by places, or just expressions
/// The left-hand side of an assignment.
#[derive_group_for_ast]
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
#[derive_group_for_ast]
pub struct ImplExpr {
    pub kind: Box<ImplExprKind>,
    pub goal: TraitGoal,
}

/// Represents all the kinds of impl expr.
///
/// # Example:
/// In the snippet below, the `clone` method on `x` corresponds to the implementation
/// of `Clone` derived for `Vec<T>` (`ImplApp`) given the `LocalBound` on `T`.
/// ```rust
/// fn f<T: Clone>(x: Vec<T>) -> Vec<T> {
///   x.clone()
/// }
/// ```
#[derive_group_for_ast]
pub enum ImplExprKind {
    /// The trait implementation being defined.
    ///
    /// # Example:
    /// The impl expr for `Type: Trait` used in `self.f()` is `Self_`.
    /// ```rust
    /// impl Trait for Type {
    ///     fn f(&self) {...}
    ///     fn g(&self) {self.f()}
    /// }
    /// ```
    Self_,
    /// A concrete `impl` block.
    ///
    /// # Example
    /// ```rust
    /// impl Clone for Type { // Consider this `impl` is called `impl0`
    ///     ...
    /// }
    /// fn f(x: Type) {
    ///     x.clone() // Here `clone` comes from `Concrete(impl0)`
    /// }
    /// ```
    Concrete(TraitGoal),
    /// A bound introduced by a generic clause.
    ///
    /// # Example:
    /// ```rust
    /// fn f<T: Clone>(x: T) -> T {
    ///   x.clone() // Here the method comes from the bound `T: Clone`
    /// }
    /// ```
    LocalBound { id: Symbol },
    /// A parent implementation.
    ///
    /// # Example:
    /// ```rust
    /// trait SubTrait: Clone {}
    /// fn f<T: SubTrait>(x: T) -> T {
    ///   x.clone() // Here the method comes from the parent of the bound `T: SubTrait`
    /// }
    /// ```
    Parent { impl_: ImplExpr, ident: ImplIdent },
    /// A projected associated implementation.
    ///
    /// # Example:
    /// In this snippet, `T::Item` is an `AssociatedType` where the subsequent `ImplExpr`
    /// is a type projection of `ITerator`.
    /// ```rust
    /// fn f<T: Iterator>(x: T) -> Option<T::Item> {
    ///     x.next()
    /// }
    /// ```
    Projection {
        impl_: ImplExpr,
        item: GlobalId,
        ident: ImplIdent,
    },
    /// An instantiation of a generic implementation.
    ///
    /// # Example:
    /// ```rust
    /// fn f<T: Clone>(x: Vec<T>) -> Vec<T> {
    ///   x.clone() // The `Clone` implementation for `Vec` is instantiated with the local bound `T: Clone`
    /// }
    /// ```
    ImplApp {
        impl_: ImplExpr,
        args: Vec<ImplExpr>,
    },
    /// The implementation provided by a dyn.
    Dyn,
    /// A trait implemented natively by rust.
    Builtin(TraitGoal),
}

/// Represents an impl item (associated type or function)
#[derive_group_for_ast]
pub struct ImplItem {
    pub meta: Metadata,
    pub generics: Generics,
    pub kind: ImplItemKind,
    pub ident: GlobalId,
}

/// Represents the kinds of impl items
#[derive_group_for_ast]
pub enum ImplItemKind {
    /// An instantiation of associated type
    Type {
        ty: Ty,
        parent_bounds: Vec<(ImplExpr, ImplIdent)>,
    },
    /// A definition for a trait function
    Fn { body: Expr, params: Vec<Param> },
}

/// Represents a trait item (associated type, fn, or default)
#[derive_group_for_ast]
pub struct TraitItem {
    pub kind: TraitItemKind,
    pub generics: Generics,
    pub ident: GlobalId,
    pub meta: Metadata,
}

/// Represents the kinds of trait items
#[derive_group_for_ast]
pub enum TraitItemKind {
    Type(Vec<ImplIdent>),
    Fn(Ty),
    Default { params: Vec<Param>, body: Expr },
}

/// A QuoteContent is a component of a quote: it can be a verbatim string, a Rust expression to embed in the quote, a pattern etc.
///
/// # Example:
/// ```rust
/// fstar!("f ${x + 3} + 10")
/// ```
/// results in `[Verbatim("f"), Expr([[x + 3]]), Verbatim(" + 10")]`
#[derive_group_for_ast]
pub enum QuoteContent {
    Verbatim(String),
    Expr(Expr),
    Pattern(Pat),
    Typ(Ty),
}

/// Represents an inlined piece of backend code
#[derive_group_for_ast]
pub struct Quote(pub Vec<QuoteContent>);

/// The origin of a quote item
#[derive_group_for_ast]
pub struct ItemQuoteOrigin {
    pub item_kind: ItemQuoteOriginKind,
    pub item_ident: GlobalId,
    pub position: ItemQuoteOriginPosition,
}

/// The kind of a quote item's origin
#[derive_group_for_ast]
pub enum ItemQuoteOriginKind {
    Fn,
    TyAlias,
    Type,
    MacroInvocation,
    Trait,
    Impl,
    Alias,
    Use,
    Quote,
    HaxError,
    NotImplementedYet,
}

/// The position of a quote item relative to its origin
#[derive_group_for_ast]
pub enum ItemQuoteOriginPosition {
    Before,
    After,
    Replace,
}

/// The kind of a loop (resugared by respective `Reconstruct...Loops` phases).
/// Useful for `FunctionalizeLoops`.
#[derive_group_for_ast]
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
        var_ty: Ty,
    },
}

/// This is a marker to describe what control flow is present in a loop.
/// It is added by phase `DropReturnBreakContinue` and the information is used in
/// `FunctionalizeLoops`. We need it to replace the control flow nodes of the AST
/// by an encoding in the `ControlFlow` enum.
#[derive_group_for_ast]
pub enum ControlFlowKind {
    BreakOnly,
    BreakOrReturn,
}

// TODO: Revisit?
#[derive_group_for_ast]
pub struct LoopState {
    pub init: Expr,
    pub body_pat: Pat,
}

// TODO: Kill some nodes (e.g. `Array`, `Tuple`)?
/// Describes the shape of an expression.
#[derive_group_for_ast]
pub enum ExprKind {
    /// If expression.
    ///
    /// # Example:
    /// `if x > 0 { 1 } else { 2 }`
    If {
        condition: Expr,
        then: Expr,
        else_: Option<Expr>,
    },

    /// Function application.
    ///
    /// # Example:
    /// `f(x, y)`
    App {
        head: Expr,
        args: Vec<Expr>,
        generic_args: Vec<GenericValue>,
        bounds_impls: Vec<ImplExpr>,
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
    },

    /// A literal value.
    ///
    /// # Example:
    /// `42`, `"hello"`
    Literal(Literal),

    /// An array literal.
    ///
    /// # Example:
    /// `[1, 2, 3]`
    Array(Vec<Expr>),

    /// A constructor application
    ///
    /// # Example:
    /// A(x)
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
    ///
    /// # Example:
    /// `(a, b)`
    Tuple(Vec<Expr>),

    /// A reference expression.
    ///
    /// # Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow {
        mutable: bool,
        inner: Expr,
    },

    /// Raw borrow
    ///
    /// # Example:
    /// `*const u8`
    AddressOf {
        mutability: Mutability,
        inner: Expr,
    },

    /// A dereference
    ///
    /// # Example:
    /// `*x`
    Deref(Expr),

    /// A `let` expression used in expressions.
    ///
    /// # Example:
    /// `let x = 1; x + 1`
    Let {
        lhs: Pat,
        rhs: Expr,
        body: Expr,
    },

    /// A global identifier.
    ///
    /// # Example:
    /// `std::mem::drop`
    GlobalId(GlobalId),

    /// A local variable.
    ///
    /// # Example:
    /// `x`
    LocalId(LocalId),

    /// Type ascription
    Ascription {
        e: Expr,
        ty: Ty,
    },

    /// Variable mutation
    ///
    /// # Example:
    /// `x = 1`
    Assign {
        lhs: Lhs,
        value: Expr,
    },

    /// Loop
    ///
    /// # Example:
    /// `loop{}`
    Loop {
        body: Expr,
        kind: LoopKind,
        state: Option<LoopState>,
        control_flow: Option<ControlFlowKind>,
        label: Option<Symbol>,
    },

    /// Break out of a loop
    ///
    /// # Example:
    /// `break`
    Break {
        value: Expr,
        label: Option<Symbol>,
    },

    /// Return from a function
    ///
    /// # Example:
    /// `return 1`
    Return {
        value: Expr,
    },

    /// Continue (go to next loop iteration)
    ///
    /// # Example:
    /// `continue`
    Continue {
        label: Option<Symbol>,
    },

    /// Closure (anonymous function)
    ///
    /// # Example:
    /// `|x| x`
    Closure {
        params: Vec<Pat>,
        body: Expr,
        captures: Vec<Expr>,
    },

    /// Block of safe or unsafe expression
    ///
    /// # Example:
    /// `unsafe {...}`
    Block {
        body: Expr,
        safety_mode: SafetyKind,
    },

    /// A quote is an inlined piece of backend code
    Quote {
        contents: Quote,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),
}

/// Represents the kinds of generic parameters
#[derive_group_for_ast]
pub enum GenericParamKind {
    Lifetime,
    Type,
    Const { ty: Ty },
}

/// Represents an instantiated trait that needs to be implemented.
///
/// # Example:
/// A bound `_: std::ops::Add<u8>`
#[derive_group_for_ast]
pub struct TraitGoal {
    /// `std::ops::Add` in the example.
    pub trait_: GlobalId,
    /// `[u8]` in the example.
    pub args: Vec<GenericValue>,
}

/// Represents a trait bound in a generic constraint
#[derive_group_for_ast]
pub struct ImplIdent {
    pub goal: TraitGoal,
    pub name: Symbol,
}

/// A projection predicate expresses a constraint over an associated type:
/// ```rust
/// fn f<T: Foo<S = String>>(...)
/// ```
/// In this example `Foo` has an associated type `S`.
#[derive_group_for_ast]
pub struct ProjectionPredicate {
    pub impl_: ImplExpr,
    pub assoc_item: GlobalId,
    pub ty: Ty,
}

/// A generic constraint (lifetime, type or projection)
#[derive_group_for_ast]
pub enum GenericConstraint {
    Lifetime(String), // TODO: Remove `String`
    Type(ImplIdent),
    Projection(ProjectionPredicate),
}

/// A generic parameter (lifetime, type parameter or const parameter)
#[derive_group_for_ast]
pub struct GenericParam {
    pub ident: LocalId,
    pub meta: Metadata,
    pub kind: GenericParamKind,
}

/// Generic parameters and constraints (contained between `<>` in function declarations)
#[derive_group_for_ast]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub constraints: Vec<GenericConstraint>,
}

/// Safety level of a function.
#[derive_group_for_ast]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}

/// Represents a single attribute.
#[derive_group_for_ast]
pub struct Attribute {
    pub kind: AttributeKind,
    pub span: Span,
}

/// Represents the kind of an attribute.
#[derive_group_for_ast]
pub enum AttributeKind {
    Tool { path: String, tokens: String },
    DocComment { kind: DocCommentKind, body: String },
}

/// Represents the kind of a doc comment.
#[derive_group_for_ast]
pub enum DocCommentKind {
    /// Single line comment (`//...`)
    Line,
    /// Block comment (`/*...*/`)
    Block,
}

/// A list of attributes.
pub type Attributes = Vec<Attribute>;

/// A type with its associated span.
#[derive_group_for_ast]
pub struct SpannedTy {
    /// Span of origin
    pub span: Span,
    /// Type
    pub ty: Ty,
}

/// A function parameter (pattern + type, e.g. `x: u8`).
#[derive_group_for_ast]
pub struct Param {
    /// Pattern part
    /// Examples: `x`, `mut y`, etc.
    pub pat: Pat,
    /// Type part with span.
    pub ty: SpannedTy,
    /// Attributes
    pub attributes: Attributes,
}

/// A variant of an enum or struct.
/// In our representation structs always have one variant with an argument for each field.
#[derive_group_for_ast]
pub struct Variant {
    /// Name of the variant
    pub name: GlobalId,
    /// Fields of this variant (named or anonymous)
    pub arguments: Vec<(GlobalId, Ty, Attributes)>,
    /// True if fields are named
    pub is_record: bool,
    /// Attributes of the variant
    pub attributes: Attributes,
}

/// A top-level item in the module.
#[derive_group_for_ast]
pub enum ItemKind {
    /// A function or constant item.
    ///
    /// # Example:```rust
    /// fn add<T: Clone>(x: i32, y: i32) -> i32 {
    ///     x + y
    /// }
    /// ```
    /// Constants are represented as functions of arity zero, while functions always have a non-zero arity.
    Fn {
        /// The identifier of the function.
        ///
        /// # Example:
        /// `add`
        name: GlobalId,
        /// The generic arguments and constraints of the function.
        ///
        /// # Example:
        /// the generic type `T` and the constraint `T: Clone`
        generics: Generics,
        /// The body of the function
        ///
        /// # Example:
        /// `x + y`
        body: Expr,
        /// The parameters of the function.
        ///
        /// # Example:
        /// `x: i32, y: i32`
        params: Vec<Param>,
        /// The safety of the function.
        safety: SafetyKind,
    },

    /// A type alias.
    ///
    /// # Example:
    /// ```rust
    /// type A = u8;
    /// ```
    TyAlias {
        /// Name of the alias
        ///
        /// # Example:
        /// `A`
        name: GlobalId,
        /// Generic arguments and constraints
        generics: Generics,
        /// Original type
        ///
        /// # Example:
        /// `u8`
        ty: Ty,
    },

    /// A type definition (struct or enum)
    ///
    /// # Example:
    /// ```rust
    /// enum A {B, C}
    /// struct S {f: u8}
    /// ```
    Type {
        /// Name of this type
        ///
        /// # Example:
        /// `A`, `S`
        name: GlobalId,
        /// Generic parameters and constraints
        generics: Generics,
        /// Variants
        ///
        /// # Example:
        /// `{B, C}`
        variants: Vec<Variant>,
        /// Is this a struct (or an enum)
        is_struct: bool,
    },

    /// A trait definition.
    ///
    /// # Example:
    /// ```rust
    /// trait T<A> {
    ///     type Assoc;
    ///     fn m(x: Self::Assoc, y: Self) -> A;
    /// }
    /// ```
    Trait {
        /// Name of this trait
        ///
        /// # Example:
        /// `T`
        name: GlobalId,
        /// Generic parameters and constraints
        ///
        /// # Example:
        /// `<A>`
        generics: Generics,
        /// Items required to implement the trait
        ///
        /// # Example:
        /// `type Assoc;`, `fn m ...;`
        items: Vec<TraitItem>,
    },

    /// A trait implementation.
    ///
    /// # Example:
    /// ```rust
    /// impl T<u8> for u16 {
    ///     type Assoc = u32;
    ///     fn m(x: u32, y: u16) -> u8 {
    ///         (x as u8) + (y as u8)
    ///     }
    /// }
    /// ```
    Impl {
        /// Generic arguments and constraints
        generics: Generics,
        /// The type we implement the trait for
        ///
        /// # Example:
        /// `u16`
        self_ty: Ty,
        /// Instantiated trait that is being implemented
        ///
        /// # Example:
        /// `T<u8>`
        of_trait: (GlobalId, Vec<GenericValue>),
        /// Items in this impl
        ///
        /// # Example:
        /// `fn m ...`, `type Assoc ...`
        items: Vec<ImplItem>,
        /// Implementations of traits required for this impl
        parent_bounds: Vec<(ImplExpr, ImplIdent)>,
        /// Safe or unsafe
        safety: SafetyKind,
    },

    /// Internal node introduced by phases, corresponds to an alias to any item.
    Alias {
        /// New name
        name: GlobalId,
        /// Original name
        item: GlobalId,
    },

    // TODO: Should we keep `Use`?
    /// A `use` statement
    Use {
        /// Path to used item(s)
        path: Vec<String>,
        /// Comes from external crate
        is_external: bool,
        /// Optional `as`
        rename: Option<String>,
    },

    /// A `Quote` node is inserted by phase TransformHaxLibInline to deal with some `hax_lib` features.
    /// For example insertion of verbatim backend code.
    Quote {
        /// Content of the quote
        quote: Quote,
        /// Description of the quote target position
        origin: ItemQuoteOrigin,
    },

    /// Fallback constructor to carry errors.
    Error(Diagnostic),

    /// Item that is not implemented yet
    NotImplementedYet,
}

/// A top-level item with metadata.
#[derive_group_for_ast]
pub struct Item {
    /// The global identifier of the item.
    pub ident: GlobalId,
    /// The kind of the item.
    pub kind: ItemKind,
    /// Source span and attributes.
    pub meta: Metadata,
}

/// Traits for utilities on AST data types
pub mod traits {
    use super::*;
    /// Marks AST data types that carry metadata (span + attributes)
    pub trait HasMetadata {
        /// Get metadata
        fn metadata(&self) -> &Metadata;
    }
    /// Marks AST data types that carry a span
    pub trait HasSpan {
        /// Get span
        fn span(&self) -> Span;
    }
    /// Marks AST data types that carry a Type
    pub trait Typed {
        /// Get type
        fn ty(&self) -> &Ty;
    }
    impl<T: HasMetadata> HasSpan for T {
        fn span(&self) -> Span {
            self.metadata().span
        }
    }

    /// Marks types of the AST that carry a kind (an enum for the actual content)
    pub trait HasKind {
        /// Type carrying the kind, should be named `<Self>Kind`
        type Kind;
        /// Get kind
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
        /// Convert to full `Expr` with type, span and attributes
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
