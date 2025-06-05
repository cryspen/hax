/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericValue<'a> {
    /// A type-level generic value.
    /// Example: `i32` in `Vec<i32>`
    Ty(PrintContext<'a, origin::Ty>),
    /// A const-level generic value.
    /// Example: `12` in `Foo<12>`
    Expr(PrintContext<'a, origin::Expr>),
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
    Int(PrintContext<'a, origin::IntKind>),
}
/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Ty<'a> {
    /// A primitive type.
    /// Example: `i32`, `bool`
    Primitive(PrintContext<'a, origin::PrimitiveTy>),
    /// A tuple type.
    /// Example: `(i32, bool)`
    Tuple(PrintContext<'a, origin::Vec<origin::Ty>>),
    /// A type application (generic type).
    /// Example: `Vec<i32>`
    App {
        head: PrintContext<'a, origin::GlobalId>,
        args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
    },
    /// A function or closure type.
    /// Example: `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow {
        inputs: PrintContext<'a, origin::Vec<origin::Ty>>,
        output: PrintContext<'a, origin::Box<origin::Ty>>,
    },
    /// A reference type.
    /// Example: `&i32`, `&mut i32`
    Ref {
        inner: PrintContext<'a, origin::Box<origin::Ty>>,
        mutable: PrintContext<'a, origin::bool>,
    },
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
    Param(PrintContext<'a, origin::LocalId>),
}
/// Extra information attached to syntax nodes.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Metadata<'a> {
    /// The location in the source code.
    pub span: PrintContext<'a, origin::Span>,
    /// Rust attributes.
    pub attrs: PrintContext<'a, origin::Attributes>,
}
/// A typed expression with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Expr<'a> {
    /// The kind of expression.
    pub kind: PrintContext<'a, origin::Box<origin::ExprKind>>,
    /// The type of this expression.
    pub ty: PrintContext<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// A typed pattern with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Pat<'a> {
    /// The kind of pattern.
    pub kind: PrintContext<'a, origin::Box<origin::PatKind>>,
    /// The type of this pattern.
    pub ty: PrintContext<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// A pattern matching arm with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Arm<'a> {
    /// The pattern of the arm.
    pub pat: PrintContext<'a, origin::Pat>,
    /// The body of the arm.
    pub body: PrintContext<'a, origin::Expr>,
    /// The optional guard of the arm.
    pub guard: PrintContext<'a, origin::Option<origin::Guard>>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// A pattern matching arm guard with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Guard<'a> {
    /// The kind of guard.
    pub kind: PrintContext<'a, origin::GuardKind>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
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
    ByRef(PrintContext<'a, origin::BorrowKind>),
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
        mutable: PrintContext<'a, origin::bool>,
        var: PrintContext<'a, origin::LocalId>,
        mode: PrintContext<'a, origin::BindingMode>,
    },
    /// A constructor pattern
    Construct {
        constructor: PrintContext<'a, origin::GlobalId>,
        is_record: PrintContext<'a, origin::bool>,
        is_struct: PrintContext<'a, origin::bool>,
        fields: PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Pat)>>,
    },
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
}
/// Represents the various kinds of pattern guards.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GuardKind<'a> {
    /// An `if let` guard
    IfLet { lhs: PrintContext<'a, origin::Pat>, rhs: PrintContext<'a, origin::Expr> },
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplExpr;
/// Describes the shape of an expression.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ExprKind<'a> {
    /// If expression.
    /// Example: `if x > 0 { 1 } else { 2 }`
    If {
        condition: PrintContext<'a, origin::Expr>,
        then: PrintContext<'a, origin::Expr>,
        else_: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    /// Function application.
    /// Example: `f(x, y)`
    App {
        head: PrintContext<'a, origin::Expr>,
        args: PrintContext<'a, origin::Vec<origin::Expr>>,
        generic_args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
        bounds_impls: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
        trait_: PrintContext<
            'a,
            origin::Option<(origin::ImplExpr, origin::Vec<origin::GenericValue>)>,
        >,
    },
    /// A literal value.
    /// Example: `42`, `"hello"`
    Literal(PrintContext<'a, origin::Literal>),
    /// An array literal.
    /// Example: `[1, 2, 3]`
    Array(PrintContext<'a, origin::Vec<origin::Expr>>),
    /// A constructor application
    /// Example: A(x)
    Construct {
        constructor: PrintContext<'a, origin::GlobalId>,
        is_record: PrintContext<'a, origin::bool>,
        is_struct: PrintContext<'a, origin::bool>,
        fields: PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Expr)>>,
        base: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    Match {
        scrutinee: PrintContext<'a, origin::Expr>,
        arms: PrintContext<'a, origin::Vec<origin::Arm>>,
    },
    /// A tuple literal.
    /// Example: `(a, b)`
    Tuple(PrintContext<'a, origin::Vec<origin::Expr>>),
    /// A reference expression.
    /// Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow {
        mutable: PrintContext<'a, origin::bool>,
        inner: PrintContext<'a, origin::Expr>,
    },
    /// A dereference: `*x`
    Deref(PrintContext<'a, origin::Expr>),
    /// A `let` expression used in expressions.
    /// Example: `let x = 1; x + 1`
    Let {
        lhs: PrintContext<'a, origin::Pat>,
        rhs: PrintContext<'a, origin::Expr>,
        body: PrintContext<'a, origin::Expr>,
    },
    /// A global identifier.
    /// Example: `std::mem::drop`
    GlobalId(PrintContext<'a, origin::GlobalId>),
    /// A local variable.
    /// Example: `x`
    LocalId(PrintContext<'a, origin::LocalId>),
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
    /// Type ascription
    Ascription { e: PrintContext<'a, origin::Expr>, ty: PrintContext<'a, origin::Ty> },
    /// Variable mutation
    /// Example: `x = 1`
    Assign {
        lhs: PrintContext<'a, origin::Expr>,
        value: PrintContext<'a, origin::Expr>,
    },
    /// Loop
    /// Example: `loop{}`
    Loop {
        body: PrintContext<'a, origin::Expr>,
        label: PrintContext<'a, origin::Option<origin::String>>,
    },
    /// Break out of a loop
    /// Example: `break`
    Break {
        value: PrintContext<'a, origin::Expr>,
        label: PrintContext<'a, origin::Option<origin::String>>,
    },
    /// Return from a function
    /// Example: `return 1`
    Return { value: PrintContext<'a, origin::Expr> },
    /// Continue (go to next loop iteration)
    /// Example: `continue`
    Continue { label: PrintContext<'a, origin::Option<origin::String>> },
    /// Closure (anonymous function)
    /// Example: `|x| x`
    Closure {
        params: PrintContext<'a, origin::Vec<origin::Pat>>,
        body: PrintContext<'a, origin::Expr>,
        captures: PrintContext<'a, origin::Vec<origin::Expr>>,
    },
}
/// Represents the kinds of generic parameters
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericParamKind<'a> {
    Lifetime,
    Type,
    Const { ty: PrintContext<'a, origin::Ty> },
}
/// Represents an instantiated trait that needs to be implemented
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct TraitGoal<'a> {
    pub trait_: PrintContext<'a, origin::GlobalId>,
    pub args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
}
/// Represents a trait bound in a generic constraint
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ImplIdent<'a> {
    pub goal: PrintContext<'a, origin::TraitGoal>,
    pub name: PrintContext<'a, origin::String>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProjectionPredicate;
/// A generic constraint (lifetime, type or projection)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericConstraint<'a> {
    Lifetime(PrintContext<'a, origin::String>),
    Type(PrintContext<'a, origin::ImplIdent>),
    Projection(PrintContext<'a, origin::ProjectionPredicate>),
}
/// A generic parameter (lifetime, type parameter or const parameter)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct GenericParam<'a> {
    pub ident: PrintContext<'a, origin::LocalId>,
    pub meta: PrintContext<'a, origin::Metadata>,
    pub kind: PrintContext<'a, origin::GenericParamKind>,
}
/// Generic parameters and constraints (contained between `<>` in function declarations)
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Generics<'a> {
    pub params: PrintContext<'a, origin::Vec<origin::GenericParam>>,
    pub constraints: PrintContext<'a, origin::Vec<origin::GenericConstraint>>,
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
    pub span: PrintContext<'a, origin::Span>,
    pub ty: PrintContext<'a, origin::Ty>,
}
/// A function parameter (pattern + type, e.g. `x: u8`).
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Param<'a> {
    /// Pattern part: `x`, `mut y`, etc.
    pub pat: PrintContext<'a, origin::Pat>,
    /// Type part with span.
    pub ty: PrintContext<'a, origin::SpannedTy>,
    /// Attributes
    pub attributes: PrintContext<'a, origin::Attributes>,
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
        name: PrintContext<'a, origin::GlobalId>,
        /// The generic arguments and constraints of the function.
        /// Example: the generic type `T` and the constraint `T: Clone`
        generics: PrintContext<'a, origin::Generics>,
        /// The body of the function
        /// Example: `x + y`
        body: PrintContext<'a, origin::Expr>,
        /// The parameters of the function.
        /// Example: `x: i32, y: i32`
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        /// The safety of the function.
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
}
/// A top-level item with metadata.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Item<'a> {
    /// The global identifier of the item.
    pub ident: PrintContext<'a, origin::GlobalId>,
    /// The kind of the item.
    pub kind: PrintContext<'a, origin::ItemKind>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredExprKind<'a> {
    ConstantApp {
        constant: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::GenericValue>,
    },
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredPatKind {}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredTy {}
impl<'a> From<GenericValue<'a>> for Node<'a> {
    fn from(item: GenericValue<'a>) -> Self {
        Self::GenericValue(item)
    }
}
impl<'a> From<PrimitiveTy<'a>> for Node<'a> {
    fn from(item: PrimitiveTy<'a>) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl<'a> From<Ty<'a>> for Node<'a> {
    fn from(item: Ty<'a>) -> Self {
        Self::Ty(item)
    }
}
impl<'a> From<Metadata<'a>> for Node<'a> {
    fn from(item: Metadata<'a>) -> Self {
        Self::Metadata(item)
    }
}
impl<'a> From<Expr<'a>> for Node<'a> {
    fn from(item: Expr<'a>) -> Self {
        Self::Expr(item)
    }
}
impl<'a> From<Pat<'a>> for Node<'a> {
    fn from(item: Pat<'a>) -> Self {
        Self::Pat(item)
    }
}
impl<'a> From<Arm<'a>> for Node<'a> {
    fn from(item: Arm<'a>) -> Self {
        Self::Arm(item)
    }
}
impl<'a> From<Guard<'a>> for Node<'a> {
    fn from(item: Guard<'a>) -> Self {
        Self::Guard(item)
    }
}
impl<'a> From<BorrowKind> for Node<'a> {
    fn from(item: BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl<'a> From<BindingMode<'a>> for Node<'a> {
    fn from(item: BindingMode<'a>) -> Self {
        Self::BindingMode(item)
    }
}
impl<'a> From<PatKind<'a>> for Node<'a> {
    fn from(item: PatKind<'a>) -> Self {
        Self::PatKind(item)
    }
}
impl<'a> From<GuardKind<'a>> for Node<'a> {
    fn from(item: GuardKind<'a>) -> Self {
        Self::GuardKind(item)
    }
}
impl<'a> From<ImplExpr> for Node<'a> {
    fn from(item: ImplExpr) -> Self {
        Self::ImplExpr(item)
    }
}
impl<'a> From<ExprKind<'a>> for Node<'a> {
    fn from(item: ExprKind<'a>) -> Self {
        Self::ExprKind(item)
    }
}
impl<'a> From<GenericParamKind<'a>> for Node<'a> {
    fn from(item: GenericParamKind<'a>) -> Self {
        Self::GenericParamKind(item)
    }
}
impl<'a> From<TraitGoal<'a>> for Node<'a> {
    fn from(item: TraitGoal<'a>) -> Self {
        Self::TraitGoal(item)
    }
}
impl<'a> From<ImplIdent<'a>> for Node<'a> {
    fn from(item: ImplIdent<'a>) -> Self {
        Self::ImplIdent(item)
    }
}
impl<'a> From<ProjectionPredicate> for Node<'a> {
    fn from(item: ProjectionPredicate) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl<'a> From<GenericConstraint<'a>> for Node<'a> {
    fn from(item: GenericConstraint<'a>) -> Self {
        Self::GenericConstraint(item)
    }
}
impl<'a> From<GenericParam<'a>> for Node<'a> {
    fn from(item: GenericParam<'a>) -> Self {
        Self::GenericParam(item)
    }
}
impl<'a> From<Generics<'a>> for Node<'a> {
    fn from(item: Generics<'a>) -> Self {
        Self::Generics(item)
    }
}
impl<'a> From<SafetyKind> for Node<'a> {
    fn from(item: SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl<'a> From<Attribute> for Node<'a> {
    fn from(item: Attribute) -> Self {
        Self::Attribute(item)
    }
}
impl<'a> From<SpannedTy<'a>> for Node<'a> {
    fn from(item: SpannedTy<'a>) -> Self {
        Self::SpannedTy(item)
    }
}
impl<'a> From<Param<'a>> for Node<'a> {
    fn from(item: Param<'a>) -> Self {
        Self::Param(item)
    }
}
impl<'a> From<ItemKind<'a>> for Node<'a> {
    fn from(item: ItemKind<'a>) -> Self {
        Self::ItemKind(item)
    }
}
impl<'a> From<Item<'a>> for Node<'a> {
    fn from(item: Item<'a>) -> Self {
        Self::Item(item)
    }
}
impl<'a> From<ResugaredExprKind<'a>> for Node<'a> {
    fn from(item: ResugaredExprKind<'a>) -> Self {
        Self::ResugaredExprKind(item)
    }
}
impl<'a> From<ResugaredPatKind> for Node<'a> {
    fn from(item: ResugaredPatKind) -> Self {
        Self::ResugaredPatKind(item)
    }
}
impl<'a> From<ResugaredTy> for Node<'a> {
    fn from(item: ResugaredTy) -> Self {
        Self::ResugaredTy(item)
    }
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Node<'a> {
    GenericValue(GenericValue<'a>),
    PrimitiveTy(PrimitiveTy<'a>),
    Ty(Ty<'a>),
    Metadata(Metadata<'a>),
    Expr(Expr<'a>),
    Pat(Pat<'a>),
    Arm(Arm<'a>),
    Guard(Guard<'a>),
    BorrowKind(BorrowKind),
    BindingMode(BindingMode<'a>),
    PatKind(PatKind<'a>),
    GuardKind(GuardKind<'a>),
    ImplExpr(ImplExpr),
    ExprKind(ExprKind<'a>),
    GenericParamKind(GenericParamKind<'a>),
    TraitGoal(TraitGoal<'a>),
    ImplIdent(ImplIdent<'a>),
    ProjectionPredicate(ProjectionPredicate),
    GenericConstraint(GenericConstraint<'a>),
    GenericParam(GenericParam<'a>),
    Generics(Generics<'a>),
    SafetyKind(SafetyKind),
    Attribute(Attribute),
    SpannedTy(SpannedTy<'a>),
    Param(Param<'a>),
    ItemKind(ItemKind<'a>),
    Item(Item<'a>),
    ResugaredExprKind(ResugaredExprKind<'a>),
    ResugaredPatKind(ResugaredPatKind),
    ResugaredTy(ResugaredTy),
}
