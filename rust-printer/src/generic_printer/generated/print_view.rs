/// Represents a generic value used in type applications (e.g., `T` in `Vec<T>`).
#[apply(derive_AST)]
pub enum GenericValue<'a> {
    /// A type-level generic value.
    ///
    /// # Example:
    /// `i32` in `Vec<i32>`
    Ty(PrintContext<'a, origin::Ty>),
    /// A const-level generic value.
    ///
    /// # Example:
    /// `12` in `Foo<12>`
    Expr(PrintContext<'a, origin::Expr>),
    /// A lifetime.
    ///
    /// # Example:
    /// `'a` in `foo<'a>`
    Lifetime,
}
/// Built-in primitive types.
#[apply(derive_AST)]
pub enum PrimitiveTy<'a> {
    /// The `bool` type.
    Bool,
    /// An integer type (e.g., `i32`, `u8`).
    Int(PrintContext<'a, origin::IntKind>),
    /// A float type (e.g. `f32`)
    Float(PrintContext<'a, origin::FloatKind>),
    /// The `char` type
    Char,
    /// The `str` type
    Str,
}
#[apply(derive_AST)]
pub struct Region;
/// Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`).
#[apply(derive_AST)]
pub enum Ty<'a> {
    /// A primitive type.
    ///
    /// # Example:
    /// `i32`, `bool`
    Primitive(PrintContext<'a, origin::PrimitiveTy>),
    /// A tuple type.
    ///
    /// # Example:
    /// `(i32, bool)`
    Tuple(PrintContext<'a, origin::Vec<origin::Ty>>),
    /// A type application (generic type).
    ///
    /// # Example:
    /// `Vec<i32>`
    App {
        head: PrintContext<'a, origin::GlobalId>,
        args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
    },
    /// A function or closure type.
    ///
    /// # Example:
    /// `fn(i32) -> bool` or `Fn(i32) -> bool`
    Arrow {
        inputs: PrintContext<'a, origin::Vec<origin::Ty>>,
        output: PrintContext<'a, origin::Box<origin::Ty>>,
    },
    /// A reference type.
    ///
    /// # Example:
    /// `&i32`, `&mut i32`
    Ref {
        inner: PrintContext<'a, origin::Box<origin::Ty>>,
        mutable: PrintContext<'a, origin::bool>,
        region: PrintContext<'a, origin::Region>,
    },
    /// A parameter type
    Param(PrintContext<'a, origin::LocalId>),
    /// A slice type.
    ///
    /// # Example:
    /// `&[i32]`
    Slice(PrintContext<'a, origin::Box<origin::Ty>>),
    /// An array type.
    ///
    /// # Example:
    /// `&[i32; 10]`
    Array {
        ty: PrintContext<'a, origin::Box<origin::Ty>>,
        length: PrintContext<'a, origin::Box<origin::Expr>>,
    },
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
        impl_: PrintContext<'a, origin::ImplExpr>,
        /// `Tr::A` in the example
        item: PrintContext<'a, origin::GlobalId>,
    },
    /// An opaque type
    ///
    /// # Example:
    /// ```rust
    /// type Foo = impl Bar;
    /// ```
    Opaque(PrintContext<'a, origin::GlobalId>),
    /// A `dyn` type
    ///
    /// # Example:
    /// ```rust
    /// dyn Tr
    /// ```
    Dyn(PrintContext<'a, origin::Vec<origin::DynTraitGoal>>),
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
}
/// A `dyn` trait. The generic arguments are known but the actual type
/// implementing the trait is known dynamically.
///
/// # Example:
/// ```rust
/// dyn Tr<A, B>
/// ```
#[apply(derive_AST)]
pub struct DynTraitGoal<'a> {
    /// `Tr` in the example above
    pub trait_: PrintContext<'a, origin::GlobalId>,
    /// `A, B` in the example above
    pub non_self_args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
}
/// Extra information attached to syntax nodes.
#[apply(derive_AST)]
pub struct Metadata<'a> {
    /// The location in the source code.
    pub span: PrintContext<'a, origin::Span>,
    /// Rust attributes.
    pub attributes: PrintContext<'a, origin::Attributes>,
}
/// A typed expression with metadata.
#[apply(derive_AST)]
pub struct Expr<'a> {
    /// The kind of expression.
    pub kind: PrintContext<'a, origin::Box<origin::ExprKind>>,
    /// The type of this expression.
    pub ty: PrintContext<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// A typed pattern with metadata.
#[apply(derive_AST)]
pub struct Pat<'a> {
    /// The kind of pattern.
    pub kind: PrintContext<'a, origin::Box<origin::PatKind>>,
    /// The type of this pattern.
    pub ty: PrintContext<'a, origin::Ty>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// A pattern matching arm with metadata.
#[apply(derive_AST)]
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
#[apply(derive_AST)]
pub struct Guard<'a> {
    /// The kind of guard.
    pub kind: PrintContext<'a, origin::GuardKind>,
    /// Source span and attributes.
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// Represents different levels of borrowing.
#[apply(derive_AST)]
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
#[apply(derive_AST)]
pub enum BindingMode<'a> {
    /// Binding by value
    ///
    /// # Example:
    /// `x`
    ByValue,
    /// Binding by reference
    ///
    /// # Example:
    /// `ref x`, `ref mut x`
    ByRef(PrintContext<'a, origin::BorrowKind>),
}
/// Represents the various kinds of patterns.
#[apply(derive_AST)]
pub enum PatKind<'a> {
    /// Wildcard pattern
    ///
    /// # Example:
    /// `_`
    Wild,
    /// An ascription pattern
    ///
    /// # Example:
    /// `p : ty`
    Ascription {
        ty: PrintContext<'a, origin::Ty>,
        typ_span: PrintContext<'a, origin::Span>,
        pat: PrintContext<'a, origin::Pat>,
    },
    /// An or pattern
    ///
    /// # Example:
    /// `p | q`
    /// Always contains at least 2 sub-patterns
    Or { sub_pats: PrintContext<'a, origin::Vec<origin::Pat>> },
    /// An array pattern
    ///
    /// # Example:
    /// `[p, q]`
    Array { args: PrintContext<'a, origin::Vec<origin::Pat>> },
    /// A dereference pattern
    ///
    /// # Example:
    /// `&p`
    Deref { sub_pat: PrintContext<'a, origin::Pat> },
    /// A constant pattern
    ///
    /// # Example:
    /// `1`
    Constant { lit: PrintContext<'a, origin::Literal> },
    /// A variable binding.
    ///
    /// # Examples:
    /// - `x` → `mutable: false`
    /// - `mut x` → `mutable: true`
    /// - `ref x` → `mode: ByRef(Shared)`
    Binding {
        mutable: PrintContext<'a, origin::bool>,
        var: PrintContext<'a, origin::LocalId>,
        mode: PrintContext<'a, origin::BindingMode>,
        sub_pat: PrintContext<'a, origin::Option<origin::Pat>>,
    },
    /// A constructor pattern
    ///
    /// # Example:
    /// ```rust
    /// Foo(x)
    /// ```
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
#[apply(derive_AST)]
pub enum GuardKind<'a> {
    /// An `if let` guard
    IfLet { lhs: PrintContext<'a, origin::Pat>, rhs: PrintContext<'a, origin::Expr> },
}
/// The left-hand side of an assignment.
#[apply(derive_AST)]
pub enum Lhs<'a> {
    LocalVar {
        var: PrintContext<'a, origin::LocalId>,
        ty: PrintContext<'a, origin::Ty>,
    },
    ArbitraryExpr(PrintContext<'a, origin::Box<origin::Expr>>),
    FieldAccessor {
        e: PrintContext<'a, origin::Box<origin::Lhs>>,
        ty: PrintContext<'a, origin::Ty>,
        field: PrintContext<'a, origin::GlobalId>,
    },
    ArrayAccessor {
        e: PrintContext<'a, origin::Box<origin::Lhs>>,
        ty: PrintContext<'a, origin::Ty>,
        index: PrintContext<'a, origin::Expr>,
    },
}
/// Represents a witness of trait implementation
#[apply(derive_AST)]
pub struct ImplExpr<'a> {
    pub kind: PrintContext<'a, origin::Box<origin::ImplExprKind>>,
    pub goal: PrintContext<'a, origin::TraitGoal>,
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
#[apply(derive_AST)]
pub enum ImplExprKind<'a> {
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
    Concrete(PrintContext<'a, origin::TraitGoal>),
    /// A bound introduced by a generic clause.
    ///
    /// # Example:
    /// ```rust
    /// fn f<T: Clone>(x: T) -> T {
    ///   x.clone() // Here the method comes from the bound `T: Clone`
    /// }
    /// ```
    LocalBound { id: PrintContext<'a, origin::Symbol> },
    /// A parent implementation.
    ///
    /// # Example:
    /// ```rust
    /// trait SubTrait: Clone {}
    /// fn f<T: SubTrait>(x: T) -> T {
    ///   x.clone() // Here the method comes from the parent of the bound `T: SubTrait`
    /// }
    /// ```
    Parent {
        impl_: PrintContext<'a, origin::ImplExpr>,
        item: PrintContext<'a, origin::GlobalId>,
    },
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
        impl_: PrintContext<'a, origin::ImplExpr>,
        item: PrintContext<'a, origin::GlobalId>,
        ident: PrintContext<'a, origin::ImplIdent>,
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
        impl_: PrintContext<'a, origin::ImplExpr>,
        args: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
    },
    /// The implementation provided by a dyn.
    Dyn,
    /// A trait implemented natively by rust.
    Builtin(PrintContext<'a, origin::TraitGoal>),
}
/// Represents an impl item (associated type or function)
#[apply(derive_AST)]
pub struct ImplItem<'a> {
    pub meta: PrintContext<'a, origin::Metadata>,
    pub generics: PrintContext<'a, origin::Generics>,
    pub kind: PrintContext<'a, origin::ImplItemKind>,
    pub ident: PrintContext<'a, origin::GlobalId>,
}
/// Represents the kinds of impl items
#[apply(derive_AST)]
pub enum ImplItemKind<'a> {
    /// An instantiation of associated type
    Type {
        ty: PrintContext<'a, origin::Ty>,
        parent_bounds: PrintContext<
            'a,
            origin::Vec<(origin::ImplExpr, origin::ImplIdent)>,
        >,
    },
    /// A definition for a trait function
    Fn {
        body: PrintContext<'a, origin::Expr>,
        params: PrintContext<'a, origin::Vec<origin::Param>>,
    },
}
/// Represents a trait item (associated type, fn, or default)
#[apply(derive_AST)]
pub struct TraitItem<'a> {
    pub kind: PrintContext<'a, origin::TraitItemKind>,
    pub generics: PrintContext<'a, origin::Generics>,
    pub ident: PrintContext<'a, origin::GlobalId>,
    pub meta: PrintContext<'a, origin::Metadata>,
}
/// Represents the kinds of trait items
#[apply(derive_AST)]
pub enum TraitItemKind<'a> {
    Type(PrintContext<'a, origin::Vec<origin::ImplIdent>>),
    Fn(PrintContext<'a, origin::Ty>),
    Default {
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        body: PrintContext<'a, origin::Expr>,
    },
}
/// A QuoteContent is a component of a quote: it can be a verbatim string, a Rust expression to embed in the quote, a pattern etc.
///
/// # Example:
/// ```rust
/// fstar!("f ${x + 3} + 10")
/// ```
/// results in `[Verbatim("f"), Expr([[x + 3]]), Verbatim(" + 10")]`
#[apply(derive_AST)]
pub enum QuoteContent<'a> {
    Verbatim(PrintContext<'a, origin::String>),
    Expr(PrintContext<'a, origin::Expr>),
    Pattern(PrintContext<'a, origin::Pat>),
    Typ(PrintContext<'a, origin::Ty>),
}
/// Represents an inlined piece of backend code
#[apply(derive_AST)]
pub struct Quote<'a>(pub PrintContext<'a, origin::Vec<origin::QuoteContent>>);
/// The origin of a quote item
#[apply(derive_AST)]
pub struct ItemQuoteOrigin<'a> {
    pub item_kind: PrintContext<'a, origin::Box<origin::ItemKind>>,
    pub item_ident: PrintContext<'a, origin::GlobalId>,
    pub position: PrintContext<'a, origin::ItemQuoteOriginPosition>,
}
/// The position of a quote item relative to its origin
#[apply(derive_AST)]
pub enum ItemQuoteOriginPosition {
    Before,
    After,
    Replace,
}
/// The kind of a loop (resugared by respective `Reconstruct...Loops` phases).
/// Useful for `FunctionalizeLoops`.
#[apply(derive_AST)]
pub enum LoopKind<'a> {
    UnconditionalLoop,
    WhileLoop { condition: PrintContext<'a, origin::Expr> },
    ForLoop { pat: PrintContext<'a, origin::Pat>, it: PrintContext<'a, origin::Expr> },
    ForIndexLoop {
        start: PrintContext<'a, origin::Expr>,
        end: PrintContext<'a, origin::Expr>,
        var: PrintContext<'a, origin::LocalId>,
        var_ty: PrintContext<'a, origin::Ty>,
    },
}
/// This is a marker to describe what control flow is present in a loop.
/// It is added by phase `DropReturnBreakContinue` and the information is used in
/// `FunctionalizeLoops`. We need it to replace the control flow nodes of the AST
/// by an encoding in the `ControlFlow` enum.
#[apply(derive_AST)]
pub enum ControlFlowKind {
    BreakOnly,
    BreakOrReturn,
}
#[apply(derive_AST)]
pub struct LoopState<'a> {
    pub init: PrintContext<'a, origin::Expr>,
    pub body_pat: PrintContext<'a, origin::Pat>,
}
/// Describes the shape of an expression.
#[apply(derive_AST)]
pub enum ExprKind<'a> {
    /// If expression.
    ///
    /// # Example:
    /// `if x > 0 { 1 } else { 2 }`
    If {
        condition: PrintContext<'a, origin::Expr>,
        then: PrintContext<'a, origin::Expr>,
        else_: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    /// Function application.
    ///
    /// # Example:
    /// `f(x, y)`
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
    ///
    /// # Example:
    /// `42`, `"hello"`
    Literal(PrintContext<'a, origin::Literal>),
    /// An array literal.
    ///
    /// # Example:
    /// `[1, 2, 3]`
    Array(PrintContext<'a, origin::Vec<origin::Expr>>),
    /// A constructor application
    ///
    /// # Example:
    /// A(x)
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
    ///
    /// # Example:
    /// `(a, b)`
    Tuple(PrintContext<'a, origin::Vec<origin::Expr>>),
    /// A reference expression.
    ///
    /// # Examples:
    /// - `&x` → `mutable: false`
    /// - `&mut x` → `mutable: true`
    Borrow {
        mutable: PrintContext<'a, origin::bool>,
        inner: PrintContext<'a, origin::Expr>,
    },
    /// Raw borrow
    ///
    /// # Example:
    /// `*const u8`
    AddressOf {
        mutability: PrintContext<'a, origin::Mutability>,
        inner: PrintContext<'a, origin::Expr>,
    },
    /// A dereference
    ///
    /// # Example:
    /// `*x`
    Deref(PrintContext<'a, origin::Expr>),
    /// A `let` expression used in expressions.
    ///
    /// # Example:
    /// `let x = 1; x + 1`
    Let {
        lhs: PrintContext<'a, origin::Pat>,
        rhs: PrintContext<'a, origin::Expr>,
        body: PrintContext<'a, origin::Expr>,
    },
    /// A global identifier.
    ///
    /// # Example:
    /// `std::mem::drop`
    GlobalId(PrintContext<'a, origin::GlobalId>),
    /// A local variable.
    ///
    /// # Example:
    /// `x`
    LocalId(PrintContext<'a, origin::LocalId>),
    /// Type ascription
    Ascription { e: PrintContext<'a, origin::Expr>, ty: PrintContext<'a, origin::Ty> },
    /// Variable mutation
    ///
    /// # Example:
    /// `x = 1`
    Assign { lhs: PrintContext<'a, origin::Lhs>, value: PrintContext<'a, origin::Expr> },
    /// Loop
    ///
    /// # Example:
    /// `loop{}`
    Loop {
        body: PrintContext<'a, origin::Expr>,
        kind: PrintContext<'a, origin::LoopKind>,
        state: PrintContext<'a, origin::Option<origin::LoopState>>,
        control_flow: PrintContext<'a, origin::Option<origin::ControlFlowKind>>,
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    /// Break out of a loop
    ///
    /// # Example:
    /// `break`
    Break {
        value: PrintContext<'a, origin::Expr>,
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    /// Return from a function
    ///
    /// # Example:
    /// `return 1`
    Return { value: PrintContext<'a, origin::Expr> },
    /// Continue (go to next loop iteration)
    ///
    /// # Example:
    /// `continue`
    Continue { label: PrintContext<'a, origin::Option<origin::Symbol>> },
    /// Closure (anonymous function)
    ///
    /// # Example:
    /// `|x| x`
    Closure {
        params: PrintContext<'a, origin::Vec<origin::Pat>>,
        body: PrintContext<'a, origin::Expr>,
        captures: PrintContext<'a, origin::Vec<origin::Expr>>,
    },
    /// A quote is an inlined piece of backend code
    Quote { contents: PrintContext<'a, origin::Quote> },
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
}
/// Represents the kinds of generic parameters
#[apply(derive_AST)]
pub enum GenericParamKind<'a> {
    Lifetime,
    Type,
    Const { ty: PrintContext<'a, origin::Ty> },
}
/// Represents an instantiated trait that needs to be implemented.
///
/// # Example:
/// A bound `_: std::ops::Add<u8>`
#[apply(derive_AST)]
pub struct TraitGoal<'a> {
    /// `std::ops::Add` in the example.
    pub trait_: PrintContext<'a, origin::GlobalId>,
    /// `[u8]` in the example.
    pub args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
}
/// Represents a trait bound in a generic constraint
#[apply(derive_AST)]
pub struct ImplIdent<'a> {
    pub goal: PrintContext<'a, origin::TraitGoal>,
    pub name: PrintContext<'a, origin::Symbol>,
}
/// A projection predicate expresses a constraint over an associated type:
/// ```rust
/// fn f<T: Foo<S = String>>(...)
/// ```
/// In this example `Foo` has an associated type `S`.
#[apply(derive_AST)]
pub struct ProjectionPredicate<'a> {
    pub impl_: PrintContext<'a, origin::ImplExpr>,
    pub assoc_item: PrintContext<'a, origin::GlobalId>,
    pub ty: PrintContext<'a, origin::Ty>,
}
/// A generic constraint (lifetime, type or projection)
#[apply(derive_AST)]
pub enum GenericConstraint<'a> {
    Lifetime(PrintContext<'a, origin::String>),
    Type(PrintContext<'a, origin::ImplIdent>),
    Projection(PrintContext<'a, origin::ProjectionPredicate>),
}
/// A generic parameter (lifetime, type parameter or const parameter)
#[apply(derive_AST)]
pub struct GenericParam<'a> {
    pub ident: PrintContext<'a, origin::LocalId>,
    pub meta: PrintContext<'a, origin::Metadata>,
    pub kind: PrintContext<'a, origin::GenericParamKind>,
}
/// Generic parameters and constraints (contained between `<>` in function declarations)
#[apply(derive_AST)]
pub struct Generics<'a> {
    pub params: PrintContext<'a, origin::Vec<origin::GenericParam>>,
    pub constraints: PrintContext<'a, origin::Vec<origin::GenericConstraint>>,
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
#[apply(derive_AST)]
pub struct Attribute<'a> {
    pub kind: PrintContext<'a, origin::AttributeKind>,
    pub span: PrintContext<'a, origin::Span>,
}
/// Represents the kind of an attribute.
#[apply(derive_AST)]
pub enum AttributeKind<'a> {
    Tool {
        path: PrintContext<'a, origin::String>,
        tokens: PrintContext<'a, origin::String>,
    },
    DocComment {
        kind: PrintContext<'a, origin::DocCommentKind>,
        body: PrintContext<'a, origin::String>,
    },
}
/// Represents the kind of a doc comment.
#[apply(derive_AST)]
pub enum DocCommentKind {
    Line,
    Block,
}
/// A list of attributes.
pub type Attributes = origin::Vec<origin::Attribute>;
/// A type with its associated span.
#[apply(derive_AST)]
pub struct SpannedTy<'a> {
    pub span: PrintContext<'a, origin::Span>,
    pub ty: PrintContext<'a, origin::Ty>,
}
/// A function parameter (pattern + type, e.g. `x: u8`).
#[apply(derive_AST)]
pub struct Param<'a> {
    /// Pattern part
    /// Examples: `x`, `mut y`, etc.
    pub pat: PrintContext<'a, origin::Pat>,
    /// Type part with span.
    pub ty: PrintContext<'a, origin::SpannedTy>,
    /// Attributes
    pub attributes: PrintContext<'a, origin::Attributes>,
}
/// A variant of an enum or struct.
/// In our representation structs always have one variant with an argument for each field.
#[apply(derive_AST)]
pub struct Variant<'a> {
    pub name: PrintContext<'a, origin::GlobalId>,
    pub arguments: PrintContext<
        'a,
        origin::Vec<(origin::GlobalId, origin::Ty, origin::Attributes)>,
    >,
    pub is_record: PrintContext<'a, origin::bool>,
    pub attributes: PrintContext<'a, origin::Attributes>,
}
/// A top-level item in the module.
#[apply(derive_AST)]
pub enum ItemKind<'a> {
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
        name: PrintContext<'a, origin::GlobalId>,
        /// The generic arguments and constraints of the function.
        ///
        /// # Example:
        /// the generic type `T` and the constraint `T: Clone`
        generics: PrintContext<'a, origin::Generics>,
        /// The body of the function
        ///
        /// # Example:
        /// `x + y`
        body: PrintContext<'a, origin::Expr>,
        /// The parameters of the function.
        ///
        /// # Example:
        /// `x: i32, y: i32`
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        /// The safety of the function.
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    /// A type alias.
    ///
    /// # Example:
    /// ```rust
    /// type A = u8;
    /// ```
    TyAlias {
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        ty: PrintContext<'a, origin::Ty>,
    },
    /// A type definition (struct or enum)
    ///
    /// # Example:
    /// ```rust
    /// enum A {B, C}
    /// struct S {f: u8}
    /// ```
    Type {
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        variants: PrintContext<'a, origin::Vec<origin::Variant>>,
        is_struct: PrintContext<'a, origin::bool>,
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
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        items: PrintContext<'a, origin::Vec<origin::TraitItem>>,
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
        generics: PrintContext<'a, origin::Generics>,
        self_ty: PrintContext<'a, origin::Ty>,
        of_trait: PrintContext<
            'a,
            origin::Vec<(origin::GlobalId, origin::GenericValue)>,
        >,
        items: PrintContext<'a, origin::Vec<origin::ImplItem>>,
        parent_bounds: PrintContext<
            'a,
            origin::Vec<(origin::ImplExpr, origin::ImplIdent)>,
        >,
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    /// Internal node introduced by phases, corresponds to an alias to any item.
    Alias {
        name: PrintContext<'a, origin::GlobalId>,
        item: PrintContext<'a, origin::GlobalId>,
    },
    /// A `use` statement
    Use {
        path: PrintContext<'a, origin::Vec<origin::String>>,
        is_external: PrintContext<'a, origin::bool>,
        rename: PrintContext<'a, origin::Option<origin::String>>,
    },
    /// A `Quote` node is inserted by phase TransformHaxLibInline to deal with some `hax_lib` features.
    /// For example insertion of verbatim backend code.
    Quote {
        quote: PrintContext<'a, origin::Quote>,
        origin: PrintContext<'a, origin::ItemQuoteOrigin>,
    },
    /// Fallback constructor to carry errors.
    Error(PrintContext<'a, origin::Diagnostic>),
    NotImplementedYet,
}
/// A top-level item with metadata.
#[apply(derive_AST)]
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
impl<'a> From<Region> for Node<'a> {
    fn from(item: Region) -> Self {
        Self::Region(item)
    }
}
impl<'a> From<Ty<'a>> for Node<'a> {
    fn from(item: Ty<'a>) -> Self {
        Self::Ty(item)
    }
}
impl<'a> From<DynTraitGoal<'a>> for Node<'a> {
    fn from(item: DynTraitGoal<'a>) -> Self {
        Self::DynTraitGoal(item)
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
impl<'a> From<Lhs<'a>> for Node<'a> {
    fn from(item: Lhs<'a>) -> Self {
        Self::Lhs(item)
    }
}
impl<'a> From<ImplExpr<'a>> for Node<'a> {
    fn from(item: ImplExpr<'a>) -> Self {
        Self::ImplExpr(item)
    }
}
impl<'a> From<ImplExprKind<'a>> for Node<'a> {
    fn from(item: ImplExprKind<'a>) -> Self {
        Self::ImplExprKind(item)
    }
}
impl<'a> From<ImplItem<'a>> for Node<'a> {
    fn from(item: ImplItem<'a>) -> Self {
        Self::ImplItem(item)
    }
}
impl<'a> From<ImplItemKind<'a>> for Node<'a> {
    fn from(item: ImplItemKind<'a>) -> Self {
        Self::ImplItemKind(item)
    }
}
impl<'a> From<TraitItem<'a>> for Node<'a> {
    fn from(item: TraitItem<'a>) -> Self {
        Self::TraitItem(item)
    }
}
impl<'a> From<TraitItemKind<'a>> for Node<'a> {
    fn from(item: TraitItemKind<'a>) -> Self {
        Self::TraitItemKind(item)
    }
}
impl<'a> From<QuoteContent<'a>> for Node<'a> {
    fn from(item: QuoteContent<'a>) -> Self {
        Self::QuoteContent(item)
    }
}
impl<'a> From<Quote<'a>> for Node<'a> {
    fn from(item: Quote<'a>) -> Self {
        Self::Quote(item)
    }
}
impl<'a> From<ItemQuoteOrigin<'a>> for Node<'a> {
    fn from(item: ItemQuoteOrigin<'a>) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl<'a> From<ItemQuoteOriginPosition> for Node<'a> {
    fn from(item: ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl<'a> From<LoopKind<'a>> for Node<'a> {
    fn from(item: LoopKind<'a>) -> Self {
        Self::LoopKind(item)
    }
}
impl<'a> From<ControlFlowKind> for Node<'a> {
    fn from(item: ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl<'a> From<LoopState<'a>> for Node<'a> {
    fn from(item: LoopState<'a>) -> Self {
        Self::LoopState(item)
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
impl<'a> From<ProjectionPredicate<'a>> for Node<'a> {
    fn from(item: ProjectionPredicate<'a>) -> Self {
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
impl<'a> From<Attribute<'a>> for Node<'a> {
    fn from(item: Attribute<'a>) -> Self {
        Self::Attribute(item)
    }
}
impl<'a> From<AttributeKind<'a>> for Node<'a> {
    fn from(item: AttributeKind<'a>) -> Self {
        Self::AttributeKind(item)
    }
}
impl<'a> From<DocCommentKind> for Node<'a> {
    fn from(item: DocCommentKind) -> Self {
        Self::DocCommentKind(item)
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
impl<'a> From<Variant<'a>> for Node<'a> {
    fn from(item: Variant<'a>) -> Self {
        Self::Variant(item)
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
#[derive()]
#[macro_rules_attribute::apply(derive_AST)]
pub enum Node<'a> {
    GenericValue(GenericValue<'a>),
    PrimitiveTy(PrimitiveTy<'a>),
    Region(Region),
    Ty(Ty<'a>),
    DynTraitGoal(DynTraitGoal<'a>),
    Metadata(Metadata<'a>),
    Expr(Expr<'a>),
    Pat(Pat<'a>),
    Arm(Arm<'a>),
    Guard(Guard<'a>),
    BorrowKind(BorrowKind),
    BindingMode(BindingMode<'a>),
    PatKind(PatKind<'a>),
    GuardKind(GuardKind<'a>),
    Lhs(Lhs<'a>),
    ImplExpr(ImplExpr<'a>),
    ImplExprKind(ImplExprKind<'a>),
    ImplItem(ImplItem<'a>),
    ImplItemKind(ImplItemKind<'a>),
    TraitItem(TraitItem<'a>),
    TraitItemKind(TraitItemKind<'a>),
    QuoteContent(QuoteContent<'a>),
    Quote(Quote<'a>),
    ItemQuoteOrigin(ItemQuoteOrigin<'a>),
    ItemQuoteOriginPosition(ItemQuoteOriginPosition),
    LoopKind(LoopKind<'a>),
    ControlFlowKind(ControlFlowKind),
    LoopState(LoopState<'a>),
    ExprKind(ExprKind<'a>),
    GenericParamKind(GenericParamKind<'a>),
    TraitGoal(TraitGoal<'a>),
    ImplIdent(ImplIdent<'a>),
    ProjectionPredicate(ProjectionPredicate<'a>),
    GenericConstraint(GenericConstraint<'a>),
    GenericParam(GenericParam<'a>),
    Generics(Generics<'a>),
    SafetyKind(SafetyKind),
    Attribute(Attribute<'a>),
    AttributeKind(AttributeKind<'a>),
    DocCommentKind(DocCommentKind),
    SpannedTy(SpannedTy<'a>),
    Param(Param<'a>),
    Variant(Variant<'a>),
    ItemKind(ItemKind<'a>),
    Item(Item<'a>),
    ResugaredExprKind(ResugaredExprKind<'a>),
    ResugaredPatKind(ResugaredPatKind),
    ResugaredTy(ResugaredTy),
}
