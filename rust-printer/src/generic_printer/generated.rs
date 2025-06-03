/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericValue<'a> {
    /// A type-level generic value.
    /// Example: `i32` in `Vec<i32>`
    Ty(Value<'a, origin::Ty>),
    /// A const-level generic value.
    /// Example: `12` in `Foo<12>`
    Expr(Value<'a, origin::Expr>),
    /// A lifetime.
    /// Example: `'a` in `foo<'a>`
    Lifetime,
}
/// Built-in primitive types.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PrimitiveTy<'a> {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(Value<'a, origin::IntKind>),
}
/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Ty<'a> {
    /// A primitive type.
    /// Example: `i32`, `bool`
    Primitive(Value<'a, origin::PrimitiveTy>),
    /// A tuple type.
    /// Example: `(i32, bool)`
    Tuple(Value<'a, origin::Vec<origin::Ty>>),
    /// A type application (generic type).
    /// Example: `Vec<i32>`
    App {
        head: Value<'a, origin::GlobalId>,
        args: Value<'a, origin::Vec<origin::GenericValue>>,
    },
    /// A function or closure type.
    /// Example: `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow {
        inputs: Value<'a, origin::Vec<origin::Ty>>,
        output: Value<'a, origin::Box<origin::Ty>>,
    },
    /// A reference type.
    /// Example: `&i32`, `&mut i32`
    Ref { inner: Value<'a, origin::Box<origin::Ty>>, mutable: Value<'a, origin::bool> },
    /// Fallback constructor to carry errors.
    Error(Value<'a, origin::Diagnostic>),
    Param(Value<'a, origin::LocalId>),
}
/// Extra information attached to syntax nodes.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Metadata<'a> {
    /// The location in the source code.
    pub span: Value<'a, origin::Span>,
    /// Rust attributes.
    pub attrs: Value<'a, origin::Attributes>,
}
/// A typed expression with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Expr<'a> {
    /// The kind of expression.
    pub kind: Value<'a, origin::Box<origin::ExprKind>>,
    /// The type of this expression.
    pub ty: Value<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: Value<'a, origin::Metadata>,
}
/// A typed pattern with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Pat<'a> {
    /// The kind of pattern.
    pub kind: Value<'a, origin::Box<origin::PatKind>>,
    /// The type of this pattern.
    pub ty: Value<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: Value<'a, origin::Metadata>,
}
/// A pattern matching arm with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Arm<'a> {
    /// The pattern of the arm.
    pub pat: Value<'a, origin::Pat>,
    /// The body of the arm.
    pub body: Value<'a, origin::Expr>,
    /// The optional guard of the arm.
    pub guard: Value<'a, origin::Option<origin::Guard>>,
    /// Source span and attributes.
    pub meta: Value<'a, origin::Metadata>,
}
/// A pattern matching arm guard with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Guard<'a> {
    /// The kind of guard.
    pub kind: Value<'a, origin::GuardKind>,
    /// Source span and attributes.
    pub meta: Value<'a, origin::Metadata>,
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
pub enum BindingMode<'a> {
    /// Binding by value: `x`
    ByValue,
    /// Binding by reference: `ref x`, `ref mut x`
    ByRef(Value<'a, origin::BorrowKind>),
}
/// Represents the various kinds of patterns.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PatKind<'a> {
    /// Wildcard pattern: `_`
    Wild,
    /// A variable binding.
    /// Examples:
    /// - `x` → `mutable: false`
    /// - `mut x` → `mutable: true`
    /// - `ref x` → `mode: ByRef(Shared)`
    Binding {
        mutable: Value<'a, origin::bool>,
        var: Value<'a, origin::LocalId>,
        mode: Value<'a, origin::BindingMode>,
    },
    /// A constructor pattern
    Construct {
        constructor: Value<'a, origin::GlobalId>,
        is_record: Value<'a, origin::bool>,
        is_struct: Value<'a, origin::bool>,
        fields: Value<'a, origin::Vec<(origin::GlobalId, origin::Pat)>>,
    },
    /// Fallback constructor to carry errors.
    Error(Value<'a, origin::Diagnostic>),
}
/// Represents the various kinds of pattern guards.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GuardKind<'a> {
    /// An `if let` guard
    IfLet { lhs: Value<'a, origin::Pat>, rhs: Value<'a, origin::Expr> },
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplExpr;
/// Describes the shape of an expression.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ExprKind<'a> {
    /// If expression.
    /// Example: `if x > 0 { 1 } else { 2 }`
    If {
        condition: Value<'a, origin::Expr>,
        then: Value<'a, origin::Expr>,
        else_: Value<'a, origin::Option<origin::Expr>>,
    },
    /// Function application.
    /// Example: `f(x, y)`
    App {
        head: Value<'a, origin::Expr>,
        args: Value<'a, origin::Vec<origin::Expr>>,
        generic_args: Value<'a, origin::Vec<origin::GenericValue>>,
        bounds_impls: Value<'a, origin::Vec<origin::ImplExpr>>,
        trait_: Value<
            'a,
            origin::Option<(origin::ImplExpr, origin::Vec<origin::GenericValue>)>,
        >,
    },
    /// A literal value.
    /// Example: `42`, `"hello"`
    Literal(Value<'a, origin::Literal>),
    /// An array literal.
    /// Example: `[1, 2, 3]`
    Array(Value<'a, origin::Vec<origin::Expr>>),
    /// A constructor application
    /// Example: A(x)
    Construct {
        constructor: Value<'a, origin::GlobalId>,
        is_record: Value<'a, origin::bool>,
        is_struct: Value<'a, origin::bool>,
        fields: Value<'a, origin::Vec<(origin::GlobalId, origin::Expr)>>,
        base: Value<'a, origin::Option<origin::Expr>>,
    },
    Match {
        scrutinee: Value<'a, origin::Expr>,
        arms: Value<'a, origin::Vec<origin::Arm>>,
    },
    /// A tuple literal.
    /// Example: `(a, b)`
    Tuple(Value<'a, origin::Vec<origin::Expr>>),
    /// A reference expression.
    /// Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow { mutable: Value<'a, origin::bool>, inner: Value<'a, origin::Expr> },
    /// A dereference: `*x`
    Deref(Value<'a, origin::Expr>),
    /// A `let` expression used in expressions.
    /// Example: `let x = 1; x + 1`
    Let {
        lhs: Value<'a, origin::Pat>,
        rhs: Value<'a, origin::Expr>,
        body: Value<'a, origin::Expr>,
    },
    /// A global identifier.
    /// Example: `std::mem::drop`
    GlobalId(Value<'a, origin::GlobalId>),
    /// A local variable.
    /// Example: `x`
    LocalId(Value<'a, origin::LocalId>),
    /// Fallback constructor to carry errors.
    Error(Value<'a, origin::Diagnostic>),
    /// Type ascription
    Ascription { e: Value<'a, origin::Expr>, ty: Value<'a, origin::Ty> },
    /// Variable mutation
    /// Example: `x = 1`
    Assign { lhs: Value<'a, origin::Expr>, value: Value<'a, origin::Expr> },
    /// Loop
    /// Example: `loop{}`
    Loop {
        body: Value<'a, origin::Expr>,
        label: Value<'a, origin::Option<origin::String>>,
    },
    /// Break out of a loop
    /// Example: `break`
    Break {
        value: Value<'a, origin::Expr>,
        label: Value<'a, origin::Option<origin::String>>,
    },
    /// Return from a function
    /// Example: `return 1`
    Return { value: Value<'a, origin::Expr> },
    /// Continue (go to next loop iteration)
    /// Example: `continue`
    Continue { label: Value<'a, origin::Option<origin::String>> },
    /// Closure (anonymous function)
    /// Example: `|x| x`
    Closure {
        params: Value<'a, origin::Vec<origin::Pat>>,
        body: Value<'a, origin::Expr>,
        captures: Value<'a, origin::Vec<origin::Expr>>,
    },
}
/// Represents the kinds of generic parameters
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericParamKind<'a> {
    Lifetime,
    Type,
    Const { ty: Value<'a, origin::Ty> },
}
/// Represents an instantiated trait that needs to be implemented
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct TraitGoal<'a> {
    trait_: Value<'a, origin::GlobalId>,
    args: Value<'a, origin::Vec<origin::GenericValue>>,
}
/// Represents a trait bound in a generic constraint
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplIdent<'a> {
    goal: Value<'a, origin::TraitGoal>,
    name: Value<'a, origin::String>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProjectionPredicate;
/// A generic constraint (lifetime, type or projection)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericConstraint<'a> {
    Lifetime(Value<'a, origin::String>),
    Type(Value<'a, origin::ImplIdent>),
    Projection(Value<'a, origin::ProjectionPredicate>),
}
/// A generic parameter (lifetime, type parameter or const parameter)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct GenericParam<'a> {
    pub ident: Value<'a, origin::LocalId>,
    pub meta: Value<'a, origin::Metadata>,
    pub kind: Value<'a, origin::GenericParamKind>,
}
/// Generic parameters and constraints (contained between `<>` in function declarations)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Generics<'a> {
    pub params: Value<'a, origin::Vec<origin::GenericParam>>,
    pub constraints: Value<'a, origin::Vec<origin::GenericConstraint>>,
}
/// Safety level of a function.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum SafetyKind {
    /// Safe function (default).
    Safe,
    /// Unsafe function.
    Unsafe,
}
/// Represents a single attribute.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Attribute;
/// A list of attributes.
pub type Attributes = origin::Vec<origin::Attribute>;
/// A type with its associated span.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct SpannedTy<'a> {
    pub span: Value<'a, origin::Span>,
    pub ty: Value<'a, origin::Ty>,
}
/// A function parameter (pattern + type, e.g. `x: u8`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Param<'a> {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: Value<'a, origin::Pat>,
    /// Type part with span.
    pub ty: Value<'a, origin::SpannedTy>,
    /// Attributes
    pub attributes: Value<'a, origin::Attributes>,
}
/// A top-level item in the module.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ItemKind<'a> {
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
        name: Value<'a, origin::GlobalId>,
        /// The generic arguments and constraints of the function.
        /// Example: the generic type `T` and the constraint `T: Clone`
        generics: Value<'a, origin::Generics>,
        /// The body of the function
        /// Example: `x + y`
        body: Value<'a, origin::Expr>,
        /// The parameters of the function.
        /// Example: `x: i32, y: i32`
        params: Value<'a, origin::Vec<origin::Param>>,
        /// The safety of the function.
        safety: Value<'a, origin::SafetyKind>,
    },
    /// Fallback constructor to carry errors.
    Error(Value<'a, origin::Diagnostic>),
}
/// A top-level item with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Item<'a> {
    /// The global identifier of the item.
    pub ident: Value<'a, origin::GlobalId>,
    /// The kind of the item.
    pub kind: Value<'a, origin::ItemKind>,
    /// Source span and attributes.
    pub meta: Value<'a, origin::Metadata>,
}
