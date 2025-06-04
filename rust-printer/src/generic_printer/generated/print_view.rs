#[doc = " Represents a generic value used in type applications (e.g., `T` in `Vec<T>`)."]
#[derive_group_for_ast]
pub enum GenericValue<'a> {
    #[doc = " A type-level generic value."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `i32` in `Vec<i32>`"]
    Ty(PrintContext<'a, origin::Ty>),
    #[doc = " A const-level generic value."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `12` in `Foo<12>`"]
    Expr(PrintContext<'a, origin::Expr>),
    #[doc = " A lifetime."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `'a` in `foo<'a>`"]
    Lifetime,
}
#[doc = " Built-in primitive types."]
#[derive_group_for_ast]
pub enum PrimitiveTy<'a> {
    #[doc = " The `bool` type."]
    Bool,
    #[doc = " An integer type (e.g., `i32`, `u8`)."]
    Int(PrintContext<'a, origin::IntKind>),
    #[doc = " A float type (e.g. `f32`)"]
    Float(PrintContext<'a, origin::FloatKind>),
    #[doc = " The `char` type"]
    Char,
    #[doc = " The `str` type"]
    Str,
}
#[derive_group_for_ast]
pub struct Region;
#[doc = " Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`)."]
#[derive_group_for_ast]
pub enum Ty<'a> {
    #[doc = " A primitive type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `i32`, `bool`"]
    Primitive(PrintContext<'a, origin::PrimitiveTy>),
    #[doc = " A tuple type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `(i32, bool)`"]
    Tuple(PrintContext<'a, origin::Vec<origin::Ty>>),
    #[doc = " A type application (generic type)."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `Vec<i32>`"]
    App {
        head: PrintContext<'a, origin::GlobalId>,
        args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
    },
    #[doc = " A function or closure type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `fn(i32) -> bool` or `Fn(i32) -> bool`"]
    Arrow {
        inputs: PrintContext<'a, origin::Vec<origin::Ty>>,
        output: PrintContext<'a, origin::Box<origin::Ty>>,
    },
    #[doc = " A reference type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&i32`, `&mut i32`"]
    Ref {
        inner: PrintContext<'a, origin::Box<origin::Ty>>,
        mutable: PrintContext<'a, origin::bool>,
        region: PrintContext<'a, origin::Region>,
    },
    #[doc = " A parameter type"]
    Param(PrintContext<'a, origin::LocalId>),
    #[doc = " A slice type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&[i32]`"]
    Slice(PrintContext<'a, origin::Box<origin::Ty>>),
    #[doc = " An array type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&[i32; 10]`"]
    Array {
        ty: PrintContext<'a, origin::Box<origin::Ty>>,
        length: PrintContext<'a, origin::Box<origin::Expr>>,
    },
    #[doc = " A raw pointer type"]
    RawPointer,
    #[doc = " An associated type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = "     fn f<T: Tr>() -> T::A {...}"]
    #[doc = " ```"]
    AssociatedType {
        #[doc = " Impl expr for `Tr<T>` in the example"]
        impl_: PrintContext<'a, origin::ImplExpr>,
        #[doc = " `Tr::A` in the example"]
        item: PrintContext<'a, origin::GlobalId>,
    },
    #[doc = " An opaque type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " type Foo = impl Bar;"]
    #[doc = " ```"]
    Opaque(PrintContext<'a, origin::GlobalId>),
    #[doc = " A `dyn` type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " dyn Tr"]
    #[doc = " ```"]
    Dyn(PrintContext<'a, origin::Vec<origin::DynTraitGoal>>),
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
}
#[doc = " A `dyn` trait. The generic arguments are known but the actual type"]
#[doc = " implementing the trait is known dynamically."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " ```rust"]
#[doc = " dyn Tr<A, B>"]
#[doc = " ```"]
#[derive_group_for_ast]
pub struct DynTraitGoal<'a> {
    #[doc = " `Tr` in the example above"]
    pub trait_: PrintContext<'a, origin::GlobalId>,
    #[doc = " `A, B` in the example above"]
    pub non_self_args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
}
#[doc = " Extra information attached to syntax nodes."]
#[derive_group_for_ast]
pub struct Metadata<'a> {
    #[doc = " The location in the source code."]
    pub span: PrintContext<'a, origin::Span>,
    #[doc = " Rust attributes."]
    pub attributes: PrintContext<'a, origin::Attributes>,
}
#[doc = " A typed expression with metadata."]
#[derive_group_for_ast]
pub struct Expr<'a> {
    #[doc = " The kind of expression."]
    pub kind: PrintContext<'a, origin::Box<origin::ExprKind>>,
    #[doc = " The type of this expression."]
    pub ty: PrintContext<'a, origin::Ty>,
    #[doc = " Source span and attributes."]
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[doc = " A typed pattern with metadata."]
#[derive_group_for_ast]
pub struct Pat<'a> {
    #[doc = " The kind of pattern."]
    pub kind: PrintContext<'a, origin::Box<origin::PatKind>>,
    #[doc = " The type of this pattern."]
    pub ty: PrintContext<'a, origin::Ty>,
    #[doc = " Source span and attributes."]
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[doc = " A pattern matching arm with metadata."]
#[derive_group_for_ast]
pub struct Arm<'a> {
    #[doc = " The pattern of the arm."]
    pub pat: PrintContext<'a, origin::Pat>,
    #[doc = " The body of the arm."]
    pub body: PrintContext<'a, origin::Expr>,
    #[doc = " The optional guard of the arm."]
    pub guard: PrintContext<'a, origin::Option<origin::Guard>>,
    #[doc = " Source span and attributes."]
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[doc = " A pattern matching arm guard with metadata."]
#[derive_group_for_ast]
pub struct Guard<'a> {
    #[doc = " The kind of guard."]
    pub kind: PrintContext<'a, origin::GuardKind>,
    #[doc = " Source span and attributes."]
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[doc = " Represents different levels of borrowing."]
#[derive_group_for_ast]
pub enum BorrowKind {
    #[doc = " Shared reference"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&x`"]
    Shared,
    #[doc = " Unique reference: this is internal to rustc"]
    Unique,
    #[doc = " Mutable reference"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&mut x`"]
    Mut,
}
#[doc = " Binding modes used in patterns."]
#[derive_group_for_ast]
pub enum BindingMode<'a> {
    #[doc = " Binding by value"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `x`"]
    ByValue,
    #[doc = " Binding by reference"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `ref x`, `ref mut x`"]
    ByRef(PrintContext<'a, origin::BorrowKind>),
}
#[doc = " Represents the various kinds of patterns."]
#[derive_group_for_ast]
pub enum PatKind<'a> {
    #[doc = " Wildcard pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `_`"]
    Wild,
    #[doc = " An ascription pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `p : ty`"]
    Ascription {
        ty: PrintContext<'a, origin::Ty>,
        typ_span: PrintContext<'a, origin::Span>,
        pat: PrintContext<'a, origin::Pat>,
    },
    #[doc = " An or pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `p | q`"]
    #[doc = " Always contains at least 2 sub-patterns"]
    Or {
        sub_pats: PrintContext<'a, origin::Vec<origin::Pat>>,
    },
    #[doc = " An array pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `[p, q]`"]
    Array {
        args: PrintContext<'a, origin::Vec<origin::Pat>>,
    },
    #[doc = " A dereference pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&p`"]
    Deref {
        sub_pat: PrintContext<'a, origin::Pat>,
    },
    #[doc = " A constant pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `1`"]
    Constant {
        lit: PrintContext<'a, origin::Literal>,
    },
    #[doc = " A variable binding."]
    #[doc = ""]
    #[doc = " # Examples:"]
    #[doc = " - `x` → `mutable: false`"]
    #[doc = " - `mut x` → `mutable: true`"]
    #[doc = " - `ref x` → `mode: ByRef(Shared)`"]
    Binding {
        mutable: PrintContext<'a, origin::bool>,
        var: PrintContext<'a, origin::LocalId>,
        mode: PrintContext<'a, origin::BindingMode>,
        sub_pat: PrintContext<'a, origin::Option<origin::Pat>>,
    },
    #[doc = " A constructor pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " Foo(x)"]
    #[doc = " ```"]
    Construct {
        constructor: PrintContext<'a, origin::GlobalId>,
        is_record: PrintContext<'a, origin::bool>,
        is_struct: PrintContext<'a, origin::bool>,
        fields: PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Pat)>>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
}
#[doc = " Represents the various kinds of pattern guards."]
#[derive_group_for_ast]
pub enum GuardKind<'a> {
    #[doc = " An `if let` guard"]
    IfLet {
        lhs: PrintContext<'a, origin::Pat>,
        rhs: PrintContext<'a, origin::Expr>,
    },
}
#[doc = " The left-hand side of an assignment."]
#[derive_group_for_ast]
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
#[doc = " Represents a witness of trait implementation"]
#[derive_group_for_ast]
pub struct ImplExpr<'a> {
    pub kind: PrintContext<'a, origin::Box<origin::ImplExprKind>>,
    pub goal: PrintContext<'a, origin::TraitGoal>,
}
#[doc = " Represents all the kinds of impl expr."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " In the snippet below, the `clone` method on `x` corresponds to the implementation"]
#[doc = " of `Clone` derived for `Vec<T>` (`ImplApp`) given the `LocalBound` on `T`."]
#[doc = " ```rust"]
#[doc = " fn f<T: Clone>(x: Vec<T>) -> Vec<T> {"]
#[doc = "   x.clone()"]
#[doc = " }"]
#[doc = " ```"]
#[derive_group_for_ast]
pub enum ImplExprKind<'a> {
    #[doc = " The trait implementation being defined."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " The impl expr for `Type: Trait` used in `self.f()` is `Self_`."]
    #[doc = " ```rust"]
    #[doc = " impl Trait for Type {"]
    #[doc = "     fn f(&self) {...}"]
    #[doc = "     fn g(&self) {self.f()}"]
    #[doc = " }"]
    #[doc = " ```"]
    Self_,
    #[doc = " A concrete `impl` block."]
    #[doc = ""]
    #[doc = " # Example"]
    #[doc = " ```rust"]
    #[doc = " impl Clone for Type { // Consider this `impl` is called `impl0`"]
    #[doc = "     ..."]
    #[doc = " }"]
    #[doc = " fn f(x: Type) {"]
    #[doc = "     x.clone() // Here `clone` comes from `Concrete(impl0)`"]
    #[doc = " }"]
    #[doc = " ```"]
    Concrete(PrintContext<'a, origin::TraitGoal>),
    #[doc = " A bound introduced by a generic clause."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " fn f<T: Clone>(x: T) -> T {"]
    #[doc = "   x.clone() // Here the method comes from the bound `T: Clone`"]
    #[doc = " }"]
    #[doc = " ```"]
    LocalBound {
        id: PrintContext<'a, origin::Symbol>,
    },
    #[doc = " A parent implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " trait SubTrait: Clone {}"]
    #[doc = " fn f<T: SubTrait>(x: T) -> T {"]
    #[doc = "   x.clone() // Here the method comes from the parent of the bound `T: SubTrait`"]
    #[doc = " }"]
    #[doc = " ```"]
    Parent {
        impl_: PrintContext<'a, origin::ImplExpr>,
        ident: PrintContext<'a, origin::ImplIdent>,
    },
    #[doc = " A projected associated implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " In this snippet, `T::Item` is an `AssociatedType` where the subsequent `ImplExpr`"]
    #[doc = " is a type projection of `ITerator`."]
    #[doc = " ```rust"]
    #[doc = " fn f<T: Iterator>(x: T) -> Option<T::Item> {"]
    #[doc = "     x.next()"]
    #[doc = " }"]
    #[doc = " ```"]
    Projection {
        impl_: PrintContext<'a, origin::ImplExpr>,
        item: PrintContext<'a, origin::GlobalId>,
        ident: PrintContext<'a, origin::ImplIdent>,
    },
    #[doc = " An instantiation of a generic implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " fn f<T: Clone>(x: Vec<T>) -> Vec<T> {"]
    #[doc = "   x.clone() // The `Clone` implementation for `Vec` is instantiated with the local bound `T: Clone`"]
    #[doc = " }"]
    #[doc = " ```"]
    ImplApp {
        impl_: PrintContext<'a, origin::ImplExpr>,
        args: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
    },
    #[doc = " The implementation provided by a dyn."]
    Dyn,
    #[doc = " A trait implemented natively by rust."]
    Builtin(PrintContext<'a, origin::TraitGoal>),
}
#[doc = " Represents an impl item (associated type or function)"]
#[derive_group_for_ast]
pub struct ImplItem<'a> {
    pub meta: PrintContext<'a, origin::Metadata>,
    pub generics: PrintContext<'a, origin::Generics>,
    pub kind: PrintContext<'a, origin::ImplItemKind>,
    pub ident: PrintContext<'a, origin::GlobalId>,
}
#[doc = " Represents the kinds of impl items"]
#[derive_group_for_ast]
pub enum ImplItemKind<'a> {
    #[doc = " An instantiation of associated type"]
    Type {
        ty: PrintContext<'a, origin::Ty>,
        parent_bounds: PrintContext<'a, origin::Vec<(origin::ImplExpr, origin::ImplIdent)>>,
    },
    #[doc = " A definition for a trait function"]
    Fn {
        body: PrintContext<'a, origin::Expr>,
        params: PrintContext<'a, origin::Vec<origin::Param>>,
    },
}
#[doc = " Represents a trait item (associated type, fn, or default)"]
#[derive_group_for_ast]
pub struct TraitItem<'a> {
    pub kind: PrintContext<'a, origin::TraitItemKind>,
    pub generics: PrintContext<'a, origin::Generics>,
    pub ident: PrintContext<'a, origin::GlobalId>,
    pub meta: PrintContext<'a, origin::Metadata>,
}
#[doc = " Represents the kinds of trait items"]
#[derive_group_for_ast]
pub enum TraitItemKind<'a> {
    Type(PrintContext<'a, origin::Vec<origin::ImplIdent>>),
    Fn(PrintContext<'a, origin::Ty>),
    Default {
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        body: PrintContext<'a, origin::Expr>,
    },
}
#[doc = " A QuoteContent is a component of a quote: it can be a verbatim string, a Rust expression to embed in the quote, a pattern etc."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " ```rust"]
#[doc = " fstar!(\"f ${x + 3} + 10\")"]
#[doc = " ```"]
#[doc = " results in `[Verbatim(\"f\"), Expr([[x + 3]]), Verbatim(\" + 10\")]`"]
#[derive_group_for_ast]
pub enum QuoteContent<'a> {
    Verbatim(PrintContext<'a, origin::String>),
    Expr(PrintContext<'a, origin::Expr>),
    Pattern(PrintContext<'a, origin::Pat>),
    Typ(PrintContext<'a, origin::Ty>),
}
#[doc = " Represents an inlined piece of backend code"]
#[derive_group_for_ast]
pub struct Quote<'a>(pub PrintContext<'a, origin::Vec<origin::QuoteContent>>);
#[doc = " The origin of a quote item"]
#[derive_group_for_ast]
pub struct ItemQuoteOrigin<'a> {
    pub item_kind: PrintContext<'a, origin::ItemQuoteOriginKind>,
    pub item_ident: PrintContext<'a, origin::GlobalId>,
    pub position: PrintContext<'a, origin::ItemQuoteOriginPosition>,
}
#[doc = " The kind of a quote item's origin"]
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
#[doc = " The position of a quote item relative to its origin"]
#[derive_group_for_ast]
pub enum ItemQuoteOriginPosition {
    Before,
    After,
    Replace,
}
#[doc = " The kind of a loop (resugared by respective `Reconstruct...Loops` phases)."]
#[doc = " Useful for `FunctionalizeLoops`."]
#[derive_group_for_ast]
pub enum LoopKind<'a> {
    UnconditionalLoop,
    WhileLoop {
        condition: PrintContext<'a, origin::Expr>,
    },
    ForLoop {
        pat: PrintContext<'a, origin::Pat>,
        it: PrintContext<'a, origin::Expr>,
    },
    ForIndexLoop {
        start: PrintContext<'a, origin::Expr>,
        end: PrintContext<'a, origin::Expr>,
        var: PrintContext<'a, origin::LocalId>,
        var_ty: PrintContext<'a, origin::Ty>,
    },
}
#[doc = " This is a marker to describe what control flow is present in a loop."]
#[doc = " It is added by phase `DropReturnBreakContinue` and the information is used in"]
#[doc = " `FunctionalizeLoops`. We need it to replace the control flow nodes of the AST"]
#[doc = " by an encoding in the `ControlFlow` enum."]
#[derive_group_for_ast]
pub enum ControlFlowKind {
    BreakOnly,
    BreakOrReturn,
}
#[derive_group_for_ast]
pub struct LoopState<'a> {
    pub init: PrintContext<'a, origin::Expr>,
    pub body_pat: PrintContext<'a, origin::Pat>,
}
#[doc = " Describes the shape of an expression."]
#[derive_group_for_ast]
pub enum ExprKind<'a> {
    #[doc = " If expression."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `if x > 0 { 1 } else { 2 }`"]
    If {
        condition: PrintContext<'a, origin::Expr>,
        then: PrintContext<'a, origin::Expr>,
        else_: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    #[doc = " Function application."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `f(x, y)`"]
    App {
        head: PrintContext<'a, origin::Expr>,
        args: PrintContext<'a, origin::Vec<origin::Expr>>,
        generic_args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
        bounds_impls: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
        trait_:
            PrintContext<'a, origin::Option<(origin::ImplExpr, origin::Vec<origin::GenericValue>)>>,
    },
    #[doc = " A literal value."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `42`, `\"hello\"`"]
    Literal(PrintContext<'a, origin::Literal>),
    #[doc = " An array literal."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `[1, 2, 3]`"]
    Array(PrintContext<'a, origin::Vec<origin::Expr>>),
    #[doc = " A constructor application"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " A(x)"]
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
    #[doc = " A tuple literal."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `(a, b)`"]
    Tuple(PrintContext<'a, origin::Vec<origin::Expr>>),
    #[doc = " A reference expression."]
    #[doc = ""]
    #[doc = " # Examples:"]
    #[doc = " - `&x` → `mutable: false`"]
    #[doc = " - `&mut x` → `mutable: true`"]
    Borrow {
        mutable: PrintContext<'a, origin::bool>,
        inner: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Raw borrow"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `*const u8`"]
    AddressOf {
        mutability: PrintContext<'a, origin::Mutability>,
        inner: PrintContext<'a, origin::Expr>,
    },
    #[doc = " A dereference"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `*x`"]
    Deref(PrintContext<'a, origin::Expr>),
    #[doc = " A `let` expression used in expressions."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `let x = 1; x + 1`"]
    Let {
        lhs: PrintContext<'a, origin::Pat>,
        rhs: PrintContext<'a, origin::Expr>,
        body: PrintContext<'a, origin::Expr>,
    },
    #[doc = " A global identifier."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `std::mem::drop`"]
    GlobalId(PrintContext<'a, origin::GlobalId>),
    #[doc = " A local variable."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `x`"]
    LocalId(PrintContext<'a, origin::LocalId>),
    #[doc = " Type ascription"]
    Ascription {
        e: PrintContext<'a, origin::Expr>,
        ty: PrintContext<'a, origin::Ty>,
    },
    #[doc = " Variable mutation"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `x = 1`"]
    Assign {
        lhs: PrintContext<'a, origin::Lhs>,
        value: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Loop"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `loop{}`"]
    Loop {
        body: PrintContext<'a, origin::Expr>,
        kind: PrintContext<'a, origin::LoopKind>,
        state: PrintContext<'a, origin::Option<origin::LoopState>>,
        control_flow: PrintContext<'a, origin::Option<origin::ControlFlowKind>>,
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " Break out of a loop"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `break`"]
    Break {
        value: PrintContext<'a, origin::Expr>,
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " Return from a function"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `return 1`"]
    Return {
        value: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Continue (go to next loop iteration)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `continue`"]
    Continue {
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " Closure (anonymous function)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `|x| x`"]
    Closure {
        params: PrintContext<'a, origin::Vec<origin::Pat>>,
        body: PrintContext<'a, origin::Expr>,
        captures: PrintContext<'a, origin::Vec<origin::Expr>>,
    },
    #[doc = " Block of safe or unsafe expression"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `unsafe {...}`"]
    Block {
        body: PrintContext<'a, origin::Expr>,
        safety_mode: PrintContext<'a, origin::SafetyKind>,
    },
    #[doc = " A quote is an inlined piece of backend code"]
    Quote {
        contents: PrintContext<'a, origin::Quote>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
}
#[doc = " Represents the kinds of generic parameters"]
#[derive_group_for_ast]
pub enum GenericParamKind<'a> {
    Lifetime,
    Type,
    Const { ty: PrintContext<'a, origin::Ty> },
}
#[doc = " Represents an instantiated trait that needs to be implemented."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " A bound `_: std::ops::Add<u8>`"]
#[derive_group_for_ast]
pub struct TraitGoal<'a> {
    #[doc = " `std::ops::Add` in the example."]
    pub trait_: PrintContext<'a, origin::GlobalId>,
    #[doc = " `[u8]` in the example."]
    pub args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
}
#[doc = " Represents a trait bound in a generic constraint"]
#[derive_group_for_ast]
pub struct ImplIdent<'a> {
    pub goal: PrintContext<'a, origin::TraitGoal>,
    pub name: PrintContext<'a, origin::Symbol>,
}
#[doc = " A projection predicate expresses a constraint over an associated type:"]
#[doc = " ```rust"]
#[doc = " fn f<T: Foo<S = String>>(...)"]
#[doc = " ```"]
#[doc = " In this example `Foo` has an associated type `S`."]
#[derive_group_for_ast]
pub struct ProjectionPredicate<'a> {
    pub impl_: PrintContext<'a, origin::ImplExpr>,
    pub assoc_item: PrintContext<'a, origin::GlobalId>,
    pub ty: PrintContext<'a, origin::Ty>,
}
#[doc = " A generic constraint (lifetime, type or projection)"]
#[derive_group_for_ast]
pub enum GenericConstraint<'a> {
    Lifetime(PrintContext<'a, origin::String>),
    Type(PrintContext<'a, origin::ImplIdent>),
    Projection(PrintContext<'a, origin::ProjectionPredicate>),
}
#[doc = " A generic parameter (lifetime, type parameter or const parameter)"]
#[derive_group_for_ast]
pub struct GenericParam<'a> {
    pub ident: PrintContext<'a, origin::LocalId>,
    pub meta: PrintContext<'a, origin::Metadata>,
    pub kind: PrintContext<'a, origin::GenericParamKind>,
}
#[doc = " Generic parameters and constraints (contained between `<>` in function declarations)"]
#[derive_group_for_ast]
pub struct Generics<'a> {
    pub params: PrintContext<'a, origin::Vec<origin::GenericParam>>,
    pub constraints: PrintContext<'a, origin::Vec<origin::GenericConstraint>>,
}
#[doc = " Safety level of a function."]
#[derive_group_for_ast]
pub enum SafetyKind {
    #[doc = " Safe function (default)."]
    Safe,
    #[doc = " Unsafe function."]
    Unsafe,
}
#[doc = " Represents a single attribute."]
#[derive_group_for_ast]
pub struct Attribute<'a> {
    pub kind: PrintContext<'a, origin::AttributeKind>,
    pub span: PrintContext<'a, origin::Span>,
}
#[doc = " Represents the kind of an attribute."]
#[derive_group_for_ast]
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
#[doc = " Represents the kind of a doc comment."]
#[derive_group_for_ast]
pub enum DocCommentKind {
    Line,
    Block,
}
#[doc = " A list of attributes."]
pub type Attributes = origin::Vec<origin::Attribute>;
#[doc = " A type with its associated span."]
#[derive_group_for_ast]
pub struct SpannedTy<'a> {
    pub span: PrintContext<'a, origin::Span>,
    pub ty: PrintContext<'a, origin::Ty>,
}
#[doc = " A function parameter (pattern + type, e.g. `x: u8`)."]
#[derive_group_for_ast]
pub struct Param<'a> {
    #[doc = " Pattern part"]
    #[doc = " Examples: `x`, `mut y`, etc."]
    pub pat: PrintContext<'a, origin::Pat>,
    #[doc = " Type part with span."]
    pub ty: PrintContext<'a, origin::SpannedTy>,
    #[doc = " Attributes"]
    pub attributes: PrintContext<'a, origin::Attributes>,
}
#[doc = " A variant of an enum or struct."]
#[doc = " In our representation structs always have one variant with an argument for each field."]
#[derive_group_for_ast]
pub struct Variant<'a> {
    pub name: PrintContext<'a, origin::GlobalId>,
    pub arguments:
        PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Ty, origin::Attributes)>>,
    pub is_record: PrintContext<'a, origin::bool>,
    pub attributes: PrintContext<'a, origin::Attributes>,
}
#[doc = " A top-level item in the module."]
#[derive_group_for_ast]
pub enum ItemKind<'a> {
    #[doc = " A function or constant item."]
    #[doc = ""]
    #[doc = " # Example:```rust"]
    #[doc = " fn add<T: Clone>(x: i32, y: i32) -> i32 {"]
    #[doc = "     x + y"]
    #[doc = " }"]
    #[doc = " ```"]
    #[doc = " Constants are represented as functions of arity zero, while functions always have a non-zero arity."]
    Fn {
        #[doc = " The identifier of the function."]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `add`"]
        name: PrintContext<'a, origin::GlobalId>,
        #[doc = " The generic arguments and constraints of the function."]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " the generic type `T` and the constraint `T: Clone`"]
        generics: PrintContext<'a, origin::Generics>,
        #[doc = " The body of the function"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `x + y`"]
        body: PrintContext<'a, origin::Expr>,
        #[doc = " The parameters of the function."]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `x: i32, y: i32`"]
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        #[doc = " The safety of the function."]
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    #[doc = " A type alias."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " type A = u8;"]
    #[doc = " ```"]
    TyAlias {
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        ty: PrintContext<'a, origin::Ty>,
    },
    #[doc = " A type definition (struct or enum)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " enum A {B, C}"]
    #[doc = " struct S {f: u8}"]
    #[doc = " ```"]
    Type {
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        variants: PrintContext<'a, origin::Vec<origin::Variant>>,
        is_struct: PrintContext<'a, origin::bool>,
    },
    #[doc = " A trait definition."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " trait T<A> {"]
    #[doc = "     type Assoc;"]
    #[doc = "     fn m(x: Self::Assoc, y: Self) -> A;"]
    #[doc = " }"]
    #[doc = " ```"]
    Trait {
        name: PrintContext<'a, origin::GlobalId>,
        generics: PrintContext<'a, origin::Generics>,
        items: PrintContext<'a, origin::Vec<origin::TraitItem>>,
    },
    #[doc = " A trait implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust"]
    #[doc = " impl T<u8> for u16 {"]
    #[doc = "     type Assoc = u32;"]
    #[doc = "     fn m(x: u32, y: u16) -> u8 {"]
    #[doc = "         (x as u8) + (y as u8)"]
    #[doc = "     }"]
    #[doc = " }"]
    #[doc = " ```"]
    Impl {
        generics: PrintContext<'a, origin::Generics>,
        self_ty: PrintContext<'a, origin::Ty>,
        of_trait: PrintContext<'a, (origin::GlobalId, origin::Vec<origin::GenericValue>)>,
        items: PrintContext<'a, origin::Vec<origin::ImplItem>>,
        parent_bounds: PrintContext<'a, origin::Vec<(origin::ImplExpr, origin::ImplIdent)>>,
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    #[doc = " Internal node introduced by phases, corresponds to an alias to any item."]
    Alias {
        name: PrintContext<'a, origin::GlobalId>,
        item: PrintContext<'a, origin::GlobalId>,
    },
    #[doc = " A `use` statement"]
    Use {
        path: PrintContext<'a, origin::Vec<origin::String>>,
        is_external: PrintContext<'a, origin::bool>,
        rename: PrintContext<'a, origin::Option<origin::String>>,
    },
    #[doc = " A `Quote` node is inserted by phase TransformHaxLibInline to deal with some `hax_lib` features."]
    #[doc = " For example insertion of verbatim backend code."]
    Quote {
        quote: PrintContext<'a, origin::Quote>,
        origin: PrintContext<'a, origin::ItemQuoteOrigin>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
    NotImplementedYet,
}
#[doc = " A top-level item with metadata."]
#[derive_group_for_ast]
pub struct Item<'a> {
    #[doc = " The global identifier of the item."]
    pub ident: PrintContext<'a, origin::GlobalId>,
    #[doc = " The kind of the item."]
    pub kind: PrintContext<'a, origin::ItemKind>,
    #[doc = " Source span and attributes."]
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
#[doc = r" An owned fragment of the print view: this `enum` can represent any node in the AST."]
#[derive_group_for_ast]
pub enum Fragment<'a> {
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
    ItemQuoteOriginKind(ItemQuoteOriginKind),
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
impl<'a> From<GenericValue<'a>> for Fragment<'a> {
    fn from(item: GenericValue<'a>) -> Self {
        Self::GenericValue(item)
    }
}
impl<'a> From<PrimitiveTy<'a>> for Fragment<'a> {
    fn from(item: PrimitiveTy<'a>) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl<'a> From<Region> for Fragment<'a> {
    fn from(item: Region) -> Self {
        Self::Region(item)
    }
}
impl<'a> From<Ty<'a>> for Fragment<'a> {
    fn from(item: Ty<'a>) -> Self {
        Self::Ty(item)
    }
}
impl<'a> From<DynTraitGoal<'a>> for Fragment<'a> {
    fn from(item: DynTraitGoal<'a>) -> Self {
        Self::DynTraitGoal(item)
    }
}
impl<'a> From<Metadata<'a>> for Fragment<'a> {
    fn from(item: Metadata<'a>) -> Self {
        Self::Metadata(item)
    }
}
impl<'a> From<Expr<'a>> for Fragment<'a> {
    fn from(item: Expr<'a>) -> Self {
        Self::Expr(item)
    }
}
impl<'a> From<Pat<'a>> for Fragment<'a> {
    fn from(item: Pat<'a>) -> Self {
        Self::Pat(item)
    }
}
impl<'a> From<Arm<'a>> for Fragment<'a> {
    fn from(item: Arm<'a>) -> Self {
        Self::Arm(item)
    }
}
impl<'a> From<Guard<'a>> for Fragment<'a> {
    fn from(item: Guard<'a>) -> Self {
        Self::Guard(item)
    }
}
impl<'a> From<BorrowKind> for Fragment<'a> {
    fn from(item: BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl<'a> From<BindingMode<'a>> for Fragment<'a> {
    fn from(item: BindingMode<'a>) -> Self {
        Self::BindingMode(item)
    }
}
impl<'a> From<PatKind<'a>> for Fragment<'a> {
    fn from(item: PatKind<'a>) -> Self {
        Self::PatKind(item)
    }
}
impl<'a> From<GuardKind<'a>> for Fragment<'a> {
    fn from(item: GuardKind<'a>) -> Self {
        Self::GuardKind(item)
    }
}
impl<'a> From<Lhs<'a>> for Fragment<'a> {
    fn from(item: Lhs<'a>) -> Self {
        Self::Lhs(item)
    }
}
impl<'a> From<ImplExpr<'a>> for Fragment<'a> {
    fn from(item: ImplExpr<'a>) -> Self {
        Self::ImplExpr(item)
    }
}
impl<'a> From<ImplExprKind<'a>> for Fragment<'a> {
    fn from(item: ImplExprKind<'a>) -> Self {
        Self::ImplExprKind(item)
    }
}
impl<'a> From<ImplItem<'a>> for Fragment<'a> {
    fn from(item: ImplItem<'a>) -> Self {
        Self::ImplItem(item)
    }
}
impl<'a> From<ImplItemKind<'a>> for Fragment<'a> {
    fn from(item: ImplItemKind<'a>) -> Self {
        Self::ImplItemKind(item)
    }
}
impl<'a> From<TraitItem<'a>> for Fragment<'a> {
    fn from(item: TraitItem<'a>) -> Self {
        Self::TraitItem(item)
    }
}
impl<'a> From<TraitItemKind<'a>> for Fragment<'a> {
    fn from(item: TraitItemKind<'a>) -> Self {
        Self::TraitItemKind(item)
    }
}
impl<'a> From<QuoteContent<'a>> for Fragment<'a> {
    fn from(item: QuoteContent<'a>) -> Self {
        Self::QuoteContent(item)
    }
}
impl<'a> From<Quote<'a>> for Fragment<'a> {
    fn from(item: Quote<'a>) -> Self {
        Self::Quote(item)
    }
}
impl<'a> From<ItemQuoteOrigin<'a>> for Fragment<'a> {
    fn from(item: ItemQuoteOrigin<'a>) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl<'a> From<ItemQuoteOriginKind> for Fragment<'a> {
    fn from(item: ItemQuoteOriginKind) -> Self {
        Self::ItemQuoteOriginKind(item)
    }
}
impl<'a> From<ItemQuoteOriginPosition> for Fragment<'a> {
    fn from(item: ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl<'a> From<LoopKind<'a>> for Fragment<'a> {
    fn from(item: LoopKind<'a>) -> Self {
        Self::LoopKind(item)
    }
}
impl<'a> From<ControlFlowKind> for Fragment<'a> {
    fn from(item: ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl<'a> From<LoopState<'a>> for Fragment<'a> {
    fn from(item: LoopState<'a>) -> Self {
        Self::LoopState(item)
    }
}
impl<'a> From<ExprKind<'a>> for Fragment<'a> {
    fn from(item: ExprKind<'a>) -> Self {
        Self::ExprKind(item)
    }
}
impl<'a> From<GenericParamKind<'a>> for Fragment<'a> {
    fn from(item: GenericParamKind<'a>) -> Self {
        Self::GenericParamKind(item)
    }
}
impl<'a> From<TraitGoal<'a>> for Fragment<'a> {
    fn from(item: TraitGoal<'a>) -> Self {
        Self::TraitGoal(item)
    }
}
impl<'a> From<ImplIdent<'a>> for Fragment<'a> {
    fn from(item: ImplIdent<'a>) -> Self {
        Self::ImplIdent(item)
    }
}
impl<'a> From<ProjectionPredicate<'a>> for Fragment<'a> {
    fn from(item: ProjectionPredicate<'a>) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl<'a> From<GenericConstraint<'a>> for Fragment<'a> {
    fn from(item: GenericConstraint<'a>) -> Self {
        Self::GenericConstraint(item)
    }
}
impl<'a> From<GenericParam<'a>> for Fragment<'a> {
    fn from(item: GenericParam<'a>) -> Self {
        Self::GenericParam(item)
    }
}
impl<'a> From<Generics<'a>> for Fragment<'a> {
    fn from(item: Generics<'a>) -> Self {
        Self::Generics(item)
    }
}
impl<'a> From<SafetyKind> for Fragment<'a> {
    fn from(item: SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl<'a> From<Attribute<'a>> for Fragment<'a> {
    fn from(item: Attribute<'a>) -> Self {
        Self::Attribute(item)
    }
}
impl<'a> From<AttributeKind<'a>> for Fragment<'a> {
    fn from(item: AttributeKind<'a>) -> Self {
        Self::AttributeKind(item)
    }
}
impl<'a> From<DocCommentKind> for Fragment<'a> {
    fn from(item: DocCommentKind) -> Self {
        Self::DocCommentKind(item)
    }
}
impl<'a> From<SpannedTy<'a>> for Fragment<'a> {
    fn from(item: SpannedTy<'a>) -> Self {
        Self::SpannedTy(item)
    }
}
impl<'a> From<Param<'a>> for Fragment<'a> {
    fn from(item: Param<'a>) -> Self {
        Self::Param(item)
    }
}
impl<'a> From<Variant<'a>> for Fragment<'a> {
    fn from(item: Variant<'a>) -> Self {
        Self::Variant(item)
    }
}
impl<'a> From<ItemKind<'a>> for Fragment<'a> {
    fn from(item: ItemKind<'a>) -> Self {
        Self::ItemKind(item)
    }
}
impl<'a> From<Item<'a>> for Fragment<'a> {
    fn from(item: Item<'a>) -> Self {
        Self::Item(item)
    }
}
impl<'a> From<ResugaredExprKind<'a>> for Fragment<'a> {
    fn from(item: ResugaredExprKind<'a>) -> Self {
        Self::ResugaredExprKind(item)
    }
}
impl<'a> From<ResugaredPatKind> for Fragment<'a> {
    fn from(item: ResugaredPatKind) -> Self {
        Self::ResugaredPatKind(item)
    }
}
impl<'a> From<ResugaredTy> for Fragment<'a> {
    fn from(item: ResugaredTy) -> Self {
        Self::ResugaredTy(item)
    }
}
