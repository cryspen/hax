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
#[doc = " Represent a Rust lifetime region."]
#[derive_group_for_ast]
pub struct Region;
#[doc = " A indirection for the representation of types."]
#[derive_group_for_ast]
pub struct Ty<'a>(pub PrintContext<'a, origin::Box<origin::TyKind>>);
#[doc = " Describes any Rust type (e.g., `i32`, `Vec<T>`, `fn(i32) -> bool`)."]
#[derive_group_for_ast]
pub enum TyKind<'a> {
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
        #[doc = " The type being applied (`Vec` in the example)."]
        head: PrintContext<'a, origin::GlobalId>,
        #[doc = " The arguments (`[i32]` in the example)."]
        args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
    },
    #[doc = " A function or closure type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `fn(i32) -> bool` or `Fn(i32) -> bool`"]
    Arrow {
        #[doc = " `i32` in the example"]
        inputs: PrintContext<'a, origin::Vec<origin::Ty>>,
        #[doc = " `bool` in the example"]
        output: PrintContext<'a, origin::Ty>,
    },
    #[doc = " A reference type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&i32`, `&mut i32`"]
    Ref {
        #[doc = " The type inside the reference"]
        inner: PrintContext<'a, origin::Ty>,
        #[doc = " Is the reference mutable?"]
        mutable: PrintContext<'a, origin::bool>,
        #[doc = " The region of this reference"]
        region: PrintContext<'a, origin::Region>,
    },
    #[doc = " A parameter type"]
    Param(PrintContext<'a, origin::LocalId>),
    #[doc = " A slice type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&[i32]`"]
    Slice(PrintContext<'a, origin::Ty>),
    #[doc = " An array type."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&[i32; 10]`"]
    Array {
        #[doc = " The type of the items of the array"]
        ty: PrintContext<'a, origin::Ty>,
        #[doc = " The length of the array"]
        length: PrintContext<'a, origin::Box<origin::Expr>>,
    },
    #[doc = " A raw pointer type"]
    RawPointer,
    #[doc = " An associated type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
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
    #[doc = " ```rust,ignore"]
    #[doc = " type Foo = impl Bar;"]
    #[doc = " ```"]
    Opaque(PrintContext<'a, origin::GlobalId>),
    #[doc = " A `dyn` type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
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
#[doc = " ```rust,ignore"]
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
        #[doc = " The inner pattern (`p` in the example)"]
        pat: PrintContext<'a, origin::Pat>,
        #[doc = " The (spanned) type ascription (`ty` in the example)"]
        ty: PrintContext<'a, origin::SpannedTy>,
    },
    #[doc = " An or pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `p | q`"]
    #[doc = " Always contains at least 2 sub-patterns"]
    Or {
        #[doc = " A vector of sub-patterns"]
        sub_pats: PrintContext<'a, origin::Vec<origin::Pat>>,
    },
    #[doc = " An array pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `[p, q]`"]
    Array {
        #[doc = " A vector of patterns"]
        args: PrintContext<'a, origin::Vec<origin::Pat>>,
    },
    #[doc = " A dereference pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `&p`"]
    Deref {
        #[doc = " The inner pattern"]
        sub_pat: PrintContext<'a, origin::Pat>,
    },
    #[doc = " A constant pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `1`"]
    Constant {
        #[doc = " The literal"]
        lit: PrintContext<'a, origin::Literal>,
    },
    #[doc = " A variable binding."]
    #[doc = ""]
    #[doc = " # Examples:"]
    #[doc = " - `x` → `mutable: false`"]
    #[doc = " - `mut x` → `mutable: true`"]
    #[doc = " - `ref x` → `mode: ByRef(Shared)`"]
    Binding {
        #[doc = " Is the binding mutable? E.g. `x` is not mutable, `mut x` is."]
        mutable: PrintContext<'a, origin::bool>,
        #[doc = " The variable introduced by the binding pattern."]
        var: PrintContext<'a, origin::LocalId>,
        #[doc = " The binding mode, e.g. [`BindingMode::Shared`] for `ref x`."]
        mode: PrintContext<'a, origin::BindingMode>,
        #[doc = " The sub-pattern, if any."]
        #[doc = " For example, this is `Some(inner_pat)` for the pattern `variable @ inner_pat`."]
        sub_pat: PrintContext<'a, origin::Option<origin::Pat>>,
    },
    #[doc = " A constructor pattern"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " Foo(x)"]
    #[doc = " ```"]
    Construct {
        #[doc = " The identifier of the constructor we are matching"]
        constructor: PrintContext<'a, origin::GlobalId>,
        #[doc = " Are we constructing a record? E.g. a struct or a variant with named fields."]
        is_record: PrintContext<'a, origin::bool>,
        #[doc = " Is this a struct? (meaning, *not* a variant from an enum)"]
        is_struct: PrintContext<'a, origin::bool>,
        #[doc = " A list of fields."]
        fields: PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Pat)>>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
}
#[doc = " Represents the various kinds of pattern guards."]
#[derive_group_for_ast]
pub enum GuardKind<'a> {
    #[doc = " An `if let` guard."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " match x {"]
    #[doc = "   Some(value) if let Some(x) = f(value) => x,"]
    #[doc = "   _ => ...,"]
    #[doc = " }"]
    #[doc = " ```"]
    IfLet {
        #[doc = " The left-hand side of the guard. `Some(x)` in the example."]
        lhs: PrintContext<'a, origin::Pat>,
        #[doc = " The right-hand side of the guard. `f(value)` in the example."]
        rhs: PrintContext<'a, origin::Expr>,
    },
}
#[doc = " The left-hand side of an assignment."]
#[derive_group_for_ast]
#[allow(missing_docs)]
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
#[doc = " An `ImplExpr` describes the full data of a trait implementation. Because of"]
#[doc = " generics, this may need to combine several concrete trait implementation"]
#[doc = " items. For example, `((1u8, 2u8), \"hello\").clone()` combines the generic"]
#[doc = " implementation of `Clone` for `(A, B)` with the concrete implementations for"]
#[doc = " `u8` and `&str`, represented as a tree."]
#[derive_group_for_ast]
pub struct ImplExpr<'a> {
    #[doc = " The impl. expression itself."]
    pub kind: PrintContext<'a, origin::Box<origin::ImplExprKind>>,
    #[doc = " The trait being implemented."]
    pub goal: PrintContext<'a, origin::TraitGoal>,
}
#[doc = " Represents all the kinds of impl expr."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " In the snippet below, the `clone` method on `x` corresponds to the implementation"]
#[doc = " of `Clone` derived for `Vec<T>` (`ImplApp`) given the `LocalBound` on `T`."]
#[doc = " ```rust,ignore"]
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
    #[doc = " ```rust,ignore"]
    #[doc = " impl Trait for Type {"]
    #[doc = "     fn f(&self) {...}"]
    #[doc = "     fn g(&self) {self.f()}"]
    #[doc = " }"]
    #[doc = " ```"]
    Self_,
    #[doc = " A concrete `impl` block."]
    #[doc = ""]
    #[doc = " # Example"]
    #[doc = " ```rust,ignore"]
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
    #[doc = " ```rust,ignore"]
    #[doc = " fn f<T: Clone>(x: T) -> T {"]
    #[doc = "   x.clone() // Here the method comes from the bound `T: Clone`"]
    #[doc = " }"]
    #[doc = " ```"]
    LocalBound {
        #[doc = " Local identifier to a bound."]
        id: PrintContext<'a, origin::Symbol>,
    },
    #[doc = " A parent implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " trait SubTrait: Clone {}"]
    #[doc = " fn f<T: SubTrait>(x: T) -> T {"]
    #[doc = "   x.clone() // Here the method comes from the parent of the bound `T: SubTrait`"]
    #[doc = " }"]
    #[doc = " ```"]
    Parent {
        #[doc = " Parent implementation"]
        impl_: PrintContext<'a, origin::ImplExpr>,
        #[doc = " Which implementation to pick in the parent"]
        ident: PrintContext<'a, origin::ImplIdent>,
    },
    #[doc = " A projected associated implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " In this snippet, `T::Item` is an `AssociatedType` where the subsequent `ImplExpr`"]
    #[doc = " is a type projection of `ITerator`."]
    #[doc = " ```rust,ignore"]
    #[doc = " fn f<T: Iterator>(x: T) -> Option<T::Item> {"]
    #[doc = "     x.next()"]
    #[doc = " }"]
    #[doc = " ```"]
    Projection {
        #[doc = " The base implementation from which we project"]
        impl_: PrintContext<'a, origin::ImplExpr>,
        #[doc = " The item in the trait implemented by `impl_`"]
        item: PrintContext<'a, origin::GlobalId>,
        #[doc = " Which implementation to pick on the item"]
        ident: PrintContext<'a, origin::ImplIdent>,
    },
    #[doc = " An instantiation of a generic implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " fn f<T: Clone>(x: Vec<T>) -> Vec<T> {"]
    #[doc = "   x.clone() // The `Clone` implementation for `Vec` is instantiated with the local bound `T: Clone`"]
    #[doc = " }"]
    #[doc = " ```"]
    ImplApp {
        #[doc = " The head of the application"]
        impl_: PrintContext<'a, origin::ImplExpr>,
        #[doc = " The arguments of the application"]
        args: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
    },
    #[doc = " The implementation provided by a dyn."]
    Dyn,
    #[doc = " A trait implemented natively by rust."]
    Builtin(PrintContext<'a, origin::TraitGoal>),
}
#[doc = " Represents an impl item (associated type or function)"]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " ```rust,ignore"]
#[doc = " impl ... {"]
#[doc = "   fn assoc_fn<T>(...) {...}"]
#[doc = " }"]
#[doc = " ```"]
#[derive_group_for_ast]
pub struct ImplItem<'a> {
    #[doc = " Metadata (span and attributes) for the impl item."]
    pub meta: PrintContext<'a, origin::Metadata>,
    #[doc = " Generics for this associated item. `T` in the example."]
    pub generics: PrintContext<'a, origin::Generics>,
    #[doc = " The associated item itself."]
    pub kind: PrintContext<'a, origin::ImplItemKind>,
    #[doc = " The unique identifier for this associated item."]
    pub ident: PrintContext<'a, origin::GlobalId>,
}
#[doc = " Represents the kinds of impl items"]
#[derive_group_for_ast]
pub enum ImplItemKind<'a> {
    #[doc = " An instantiation of associated type"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " The associated type `Error` in the following example."]
    #[doc = " ```rust,ignore"]
    #[doc = " impl TryInto for ... {"]
    #[doc = "   type Error = u8;"]
    #[doc = " }"]
    #[doc = " ```"]
    Type {
        #[doc = " The type expression, `u8` in the example."]
        ty: PrintContext<'a, origin::Ty>,
        #[doc = " The parent bounds. In the example, there are none (in the definition"]
        #[doc = " of `TryInto`, there is no `Error: Something` in the associated type"]
        #[doc = " definition)."]
        parent_bounds: PrintContext<'a, origin::Vec<(origin::ImplExpr, origin::ImplIdent)>>,
    },
    #[doc = " A definition for a trait function"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " The associated function `into` in the following example."]
    #[doc = " ```rust,ignore"]
    #[doc = " impl Into for T {"]
    #[doc = "   fn into(&self) -> T {...}"]
    #[doc = " }"]
    #[doc = " ```"]
    Fn {
        #[doc = " The body of the associated function (`...` in the example)"]
        body: PrintContext<'a, origin::Expr>,
        #[doc = " The list of the argument for the associated function (`&self` in the example)."]
        params: PrintContext<'a, origin::Vec<origin::Param>>,
    },
}
#[doc = " Represents a trait item (associated type, fn, or default)"]
#[derive_group_for_ast]
pub struct TraitItem<'a> {
    #[doc = " Source span and attributes."]
    pub meta: PrintContext<'a, origin::Metadata>,
    #[doc = " The kind of trait item we are dealing with (an associated type or function)."]
    pub kind: PrintContext<'a, origin::TraitItemKind>,
    #[doc = " The generics this associated item carries."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " The generics `<B>` on `f`, **not** `<A>`."]
    #[doc = " ```rust,ignore"]
    #[doc = " trait<A> ... {"]
    #[doc = "    fn f<B>(){}"]
    #[doc = " }"]
    #[doc = " ```"]
    pub generics: PrintContext<'a, origin::Generics>,
    #[doc = " The identifier of the associateed item."]
    pub ident: PrintContext<'a, origin::GlobalId>,
}
#[doc = " Represents the kinds of trait items"]
#[derive_group_for_ast]
pub enum TraitItemKind<'a> {
    #[doc = " An associated type"]
    Type(PrintContext<'a, origin::Vec<origin::ImplIdent>>),
    #[doc = " An associated function"]
    Fn(PrintContext<'a, origin::Ty>),
    #[doc = " An associated function with a default body."]
    #[doc = " A arrow type (like what is given in `TraitItemKind::Ty`) can be"]
    #[doc = " reconstructed using the types of the parameters and of the body."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " impl ... {"]
    #[doc = "   fn f(x: u8) -> u8 { x + 2 }"]
    #[doc = " }"]
    #[doc = " ```"]
    Default {
        #[doc = " The parameters of the associated function (`[x: u8]` in the example)."]
        params: PrintContext<'a, origin::Vec<origin::Param>>,
        #[doc = " The default body of the associated function (`x + 2` in the example)."]
        body: PrintContext<'a, origin::Expr>,
    },
}
#[doc = " A QuoteContent is a component of a quote: it can be a verbatim string, a Rust expression to embed in the quote, a pattern etc."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " ```rust,ignore"]
#[doc = " fstar!(\"f ${x + 3} + 10\")"]
#[doc = " ```"]
#[doc = " results in `[Verbatim(\"f\"), Expr([[x + 3]]), Verbatim(\" + 10\")]`"]
#[derive_group_for_ast]
pub enum QuoteContent<'a> {
    #[doc = " A verbatim chunk of backend code."]
    Verbatim(PrintContext<'a, origin::String>),
    #[doc = " A Rust expression to inject in the quote."]
    Expr(PrintContext<'a, origin::Expr>),
    #[doc = " A Rust pattern to inject in the quote."]
    Pattern(PrintContext<'a, origin::Pat>),
    #[doc = " A Rust type to inject in the quote."]
    Ty(PrintContext<'a, origin::Ty>),
}
#[doc = " Represents an inlined piece of backend code"]
#[derive_group_for_ast]
pub struct Quote<'a>(pub PrintContext<'a, origin::Vec<origin::QuoteContent>>);
#[doc = " The origin of a quote item."]
#[derive_group_for_ast]
pub struct ItemQuoteOrigin<'a> {
    #[doc = " From which kind of item this quote was placed on?"]
    pub item_kind: PrintContext<'a, origin::ItemQuoteOriginKind>,
    #[doc = " From what item this quote was placed on?"]
    pub item_ident: PrintContext<'a, origin::GlobalId>,
    #[doc = " What was the position of the quote?"]
    pub position: PrintContext<'a, origin::ItemQuoteOriginPosition>,
}
#[doc = " The kind of a quote item's origin"]
#[derive_group_for_ast]
pub enum ItemQuoteOriginKind {
    #[doc = " A function"]
    Fn,
    #[doc = " A type alias"]
    TyAlias,
    #[doc = " A type definition (`enum`, `union`, `struct`)"]
    Type,
    #[doc = " A macro invocation"]
    #[doc = " TODO: drop"]
    MacroInvocation,
    #[doc = " A trait definition"]
    Trait,
    #[doc = " An `impl` block"]
    Impl,
    #[doc = " An alias"]
    Alias,
    #[doc = " A `use`"]
    Use,
    #[doc = " A quote"]
    Quote,
    #[doc = " An error"]
    HaxError,
    #[doc = " Something unknown"]
    NotImplementedYet,
}
#[doc = " The position of a quote item relative to its origin"]
#[derive_group_for_ast]
pub enum ItemQuoteOriginPosition {
    #[doc = " The quote was placed before an item"]
    Before,
    #[doc = " The quote was placed after an item"]
    After,
    #[doc = " The quote replaces an item"]
    Replace,
}
#[doc = " The kind of a loop (resugared by respective `Reconstruct...Loops` phases)."]
#[doc = " Useful for `FunctionalizeLoops`."]
#[derive_group_for_ast]
pub enum LoopKind<'a> {
    #[doc = " An unconditional loop."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `loop { ... }`"]
    UnconditionalLoop,
    #[doc = " A while loop."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " while(condition) { ... }"]
    #[doc = " ```"]
    WhileLoop {
        #[doc = " The boolean condition"]
        condition: PrintContext<'a, origin::Expr>,
    },
    #[doc = " A for loop."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " for i in iterator { ... }"]
    #[doc = " ```"]
    ForLoop {
        #[doc = " The pattern of the for loop (`i` in the example)."]
        pat: PrintContext<'a, origin::Pat>,
        #[doc = " The iterator we're looping on (`iterator` in the example)."]
        iterator: PrintContext<'a, origin::Expr>,
    },
    #[doc = " A specialized for loop on a range."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " for i in start..end {"]
    #[doc = "   ..."]
    #[doc = " }"]
    #[doc = " ```"]
    ForIndexLoop {
        #[doc = " Where the range begins (`start` in the example)."]
        start: PrintContext<'a, origin::Expr>,
        #[doc = " Where the range ends (`end` in the example)."]
        end: PrintContext<'a, origin::Expr>,
        #[doc = " The binding used for the iteration."]
        var: PrintContext<'a, origin::LocalId>,
        #[doc = " The type of the binding `var`."]
        var_ty: PrintContext<'a, origin::Ty>,
    },
}
#[doc = " This is a marker to describe what control flow is present in a loop."]
#[doc = " It is added by phase `DropReturnBreakContinue` and the information is used in"]
#[doc = " `FunctionalizeLoops`. We need it to replace the control flow nodes of the AST"]
#[doc = " by an encoding in the `ControlFlow` enum."]
#[derive_group_for_ast]
pub enum ControlFlowKind {
    #[doc = " Contains no `return`, maybe some `break`s"]
    BreakOnly,
    #[doc = " Contains both at least one `return` and maybe some `break`s"]
    BreakOrReturn,
}
#[doc = " Represent explicit mutation context for a loop."]
#[doc = " This is useful to make loops pure."]
#[derive_group_for_ast]
pub struct LoopState<'a> {
    #[doc = " The initial state of the loop."]
    pub init: PrintContext<'a, origin::Expr>,
    #[doc = " The pattern that destructures the state of the loop."]
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
        #[doc = " The boolean condition (`x > 0` in the example)."]
        condition: PrintContext<'a, origin::Expr>,
        #[doc = " The then branch (`1` in the example)."]
        then: PrintContext<'a, origin::Expr>,
        #[doc = " An optional else branch (`Some(2)`in the example)."]
        else_: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    #[doc = " Function application."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `f(x, y)`"]
    App {
        #[doc = " The head of the function application (or, which function do we apply?)."]
        head: PrintContext<'a, origin::Expr>,
        #[doc = " The arguments applied to the function."]
        args: PrintContext<'a, origin::Vec<origin::Expr>>,
        #[doc = " The generic arguments applied to the function."]
        generic_args: PrintContext<'a, origin::Vec<origin::GenericValue>>,
        #[doc = " If the function requires generic bounds to be called, `bounds_impls`"]
        #[doc = " is a vector of impl. expressions for those bounds."]
        bounds_impls: PrintContext<'a, origin::Vec<origin::ImplExpr>>,
        #[doc = " If we apply an associated function, contains the impl. expr used."]
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
    #[doc = " ```rust,ignore"]
    #[doc = " MyEnum::MyVariant { x : 1, ...base }"]
    #[doc = " ``````"]
    Construct {
        #[doc = " The identifier of the constructor we are building (`MyEnum::MyVariant` in the example)."]
        constructor: PrintContext<'a, origin::GlobalId>,
        #[doc = " Are we constructing a record? E.g. a struct or a variant with named fields. (`true` in the example)"]
        is_record: PrintContext<'a, origin::bool>,
        #[doc = " Is this a struct? Neaning, *not* a variant from an enum. (`false` in the example)"]
        is_struct: PrintContext<'a, origin::bool>,
        #[doc = " A list of fields (`[(x, 1)]` in the example)."]
        fields: PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Expr)>>,
        #[doc = " The base expression, if any. (`Some(base)` in the example)"]
        base: PrintContext<'a, origin::Option<origin::Expr>>,
    },
    #[doc = " A `match`` expression."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " match x {"]
    #[doc = "     pat1 => expr1,"]
    #[doc = "     pat2 => expr2,"]
    #[doc = " }"]
    #[doc = " ```"]
    Match {
        #[doc = " The expression on which we are matching. (`x` in the example)"]
        scrutinee: PrintContext<'a, origin::Expr>,
        #[doc = " The arms of the match. (`pat1 => expr1` and `pat2 => expr2` in the example)"]
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
        #[doc = " Is the borrow mutable?"]
        mutable: PrintContext<'a, origin::bool>,
        #[doc = " The expression we are borrowing"]
        inner: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Raw borrow"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `*const u8`"]
    AddressOf {
        #[doc = " Is the raw pointer mutable?"]
        mutable: PrintContext<'a, origin::bool>,
        #[doc = " The expression on which we take a pointer"]
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
        #[doc = " The left-hand side of the `let` expression. (`x` in the example)"]
        lhs: PrintContext<'a, origin::Pat>,
        #[doc = " The right-hand side of the `let` expression. (`1` in the example)"]
        rhs: PrintContext<'a, origin::Expr>,
        #[doc = " The body of the `let`. (`x + 1` in the example)"]
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
        #[doc = " The expression being ascribed."]
        e: PrintContext<'a, origin::Expr>,
        #[doc = " The type"]
        ty: PrintContext<'a, origin::Ty>,
    },
    #[doc = " Variable mutation"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `x = 1`"]
    Assign {
        #[doc = " the left-hand side (place) of the assign"]
        lhs: PrintContext<'a, origin::Lhs>,
        #[doc = " The value we are assigning"]
        value: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Loop"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `'label: loop { body }`"]
    Loop {
        #[doc = " The body of the loop."]
        body: PrintContext<'a, origin::Expr>,
        #[doc = " The kind of loop (e.g. `while`, `loop`, `for`...)."]
        kind: PrintContext<'a, origin::LoopKind>,
        #[doc = " An optional loop state, that makes explicit the state mutated by the"]
        #[doc = " loop."]
        state: PrintContext<'a, origin::Option<origin::LoopState>>,
        #[doc = " What kind of control flow is performed by this loop?"]
        control_flow: PrintContext<'a, origin::Option<origin::ControlFlowKind>>,
        #[doc = " Optional loop label."]
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " The `break` exppression, that breaks out of a loop."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `break 'label 3`"]
    Break {
        #[doc = " The value we break with. By default, this is `()`."]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " ```rust,ignore"]
        #[doc = " loop { break 3; } + 3"]
        #[doc = " ```"]
        value: PrintContext<'a, origin::Expr>,
        #[doc = " What loop shall we break? By default, the parent enclosing loop."]
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " Return from a function."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `return 1`"]
    Return {
        #[doc = " The expression we return (`1` in the example)."]
        value: PrintContext<'a, origin::Expr>,
    },
    #[doc = " Continue (go to next loop iteration)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `continue 'label`"]
    Continue {
        #[doc = " The loop we continue."]
        label: PrintContext<'a, origin::Option<origin::Symbol>>,
    },
    #[doc = " Closure (anonymous function)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `|x| x`"]
    Closure {
        #[doc = " The parameters of the closure"]
        params: PrintContext<'a, origin::Vec<origin::Pat>>,
        #[doc = " The body of the closure"]
        body: PrintContext<'a, origin::Expr>,
        #[doc = " The captured expressions"]
        captures: PrintContext<'a, origin::Vec<origin::Expr>>,
    },
    #[doc = " Block of safe or unsafe expression"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " `unsafe { ... }`"]
    Block {
        #[doc = " The body of the block."]
        body: PrintContext<'a, origin::Expr>,
        #[doc = " The safety of the block."]
        safety_mode: PrintContext<'a, origin::SafetyKind>,
    },
    #[doc = " A quote is an inlined piece of backend code."]
    Quote {
        #[doc = " The contents of the quote."]
        contents: PrintContext<'a, origin::Quote>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
}
#[doc = " Represents the kinds of generic parameters"]
#[derive_group_for_ast]
pub enum GenericParamKind<'a> {
    #[doc = " A generic lifetime"]
    Lifetime,
    #[doc = " A generic type"]
    Type,
    #[doc = " A generic constant"]
    Const {
        #[doc = " The type of the generic constant"]
        ty: PrintContext<'a, origin::Ty>,
    },
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
    #[doc = " The trait goal of this impl identifier"]
    pub goal: PrintContext<'a, origin::TraitGoal>,
    #[doc = " The name itself"]
    pub name: PrintContext<'a, origin::Symbol>,
}
#[doc = " A projection predicate expresses a constraint over an associated type:"]
#[doc = " ```rust,ignore"]
#[doc = " fn f<T: Foo<S = String>>(...)"]
#[doc = " ```"]
#[doc = " In this example `Foo` has an associated type `S`."]
#[derive_group_for_ast]
pub struct ProjectionPredicate<'a> {
    #[doc = " The impl expression we project from"]
    pub impl_: PrintContext<'a, origin::ImplExpr>,
    #[doc = " The associated type being projected"]
    pub assoc_item: PrintContext<'a, origin::GlobalId>,
    #[doc = " The equality constraint on the associated type"]
    pub ty: PrintContext<'a, origin::Ty>,
}
#[doc = " A generic constraint (lifetime, type or projection)"]
#[derive_group_for_ast]
pub enum GenericConstraint<'a> {
    #[doc = " A lifetime"]
    Lifetime(PrintContext<'a, origin::String>),
    #[doc = " A type"]
    Type(PrintContext<'a, origin::ImplIdent>),
    #[doc = " A projection"]
    Projection(PrintContext<'a, origin::ProjectionPredicate>),
}
#[doc = " A generic parameter (lifetime, type parameter or const parameter)"]
#[derive_group_for_ast]
pub struct GenericParam<'a> {
    #[doc = " The local identifier for the generic parameter"]
    pub ident: PrintContext<'a, origin::LocalId>,
    #[doc = " Metadata (span and attributes) for the generic parameter."]
    pub meta: PrintContext<'a, origin::Metadata>,
    #[doc = " The kind of generic parameter."]
    pub kind: PrintContext<'a, origin::GenericParamKind>,
}
#[doc = " Generic parameters and constraints (contained between `<>` in function declarations)"]
#[derive_group_for_ast]
pub struct Generics<'a> {
    #[doc = " A vector of genreric parameters."]
    pub params: PrintContext<'a, origin::Vec<origin::GenericParam>>,
    #[doc = " A vector of genreric constraints."]
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
    #[doc = " The kind of attribute (a comment, a tool attribute?)."]
    pub kind: PrintContext<'a, origin::AttributeKind>,
    #[doc = " The span of the attribute."]
    pub span: PrintContext<'a, origin::Span>,
}
#[doc = " Represents the kind of an attribute."]
#[derive_group_for_ast]
pub enum AttributeKind<'a> {
    #[doc = " A tool attribute `#[path(tokens)]`"]
    Tool {
        #[doc = " The path to the tool"]
        path: PrintContext<'a, origin::String>,
        #[doc = " The payload        "]
        tokens: PrintContext<'a, origin::String>,
    },
    #[doc = " A doc comment"]
    DocComment {
        #[doc = " What kind of comment? (single lines, block)"]
        kind: PrintContext<'a, origin::DocCommentKind>,
        #[doc = " The contents of the comment"]
        body: PrintContext<'a, origin::String>,
    },
}
#[doc = " Represents the kind of a doc comment."]
#[derive_group_for_ast]
pub enum DocCommentKind {
    #[doc = " Single line comment (`//...`)"]
    Line,
    #[doc = " Block comment (`/*...*/`)"]
    Block,
}
#[doc = " A list of attributes."]
pub type Attributes = origin::Vec<origin::Attribute>;
#[doc = " A type with its associated span."]
#[derive_group_for_ast]
pub struct SpannedTy<'a> {
    #[doc = " The span of the type"]
    pub span: PrintContext<'a, origin::Span>,
    #[doc = " The type itself"]
    pub ty: PrintContext<'a, origin::Ty>,
}
#[doc = " A function or closure parameter."]
#[doc = ""]
#[doc = " # Example:"]
#[doc = " ```rust,ignore"]
#[doc = " (mut x, y): (T, u8)"]
#[doc = " ```"]
#[derive_group_for_ast]
pub struct Param<'a> {
    #[doc = " The pattern part (left-hand side) of a parameter (`(mut x, y)` in the example)."]
    pub pat: PrintContext<'a, origin::Pat>,
    #[doc = " The type part (right-rand side) of a parameter (`(T, u8)` in the example)."]
    pub ty: PrintContext<'a, origin::Ty>,
    #[doc = " The span of the type part (if available)."]
    pub ty_span: PrintContext<'a, origin::Option<origin::Span>>,
    #[doc = " Optionally, some attributes present on the parameter."]
    pub attributes: PrintContext<'a, origin::Attributes>,
}
#[doc = " A variant of an enum or struct."]
#[doc = " In our representation structs always have one variant with an argument for each field."]
#[derive_group_for_ast]
pub struct Variant<'a> {
    #[doc = " Name of the variant"]
    pub name: PrintContext<'a, origin::GlobalId>,
    #[doc = " Fields of this variant (named or anonymous)"]
    pub arguments:
        PrintContext<'a, origin::Vec<(origin::GlobalId, origin::Ty, origin::Attributes)>>,
    #[doc = " True if fields are named"]
    pub is_record: PrintContext<'a, origin::bool>,
    #[doc = " Attributes of the variant"]
    pub attributes: PrintContext<'a, origin::Attributes>,
}
#[doc = " A top-level item in the module."]
#[derive_group_for_ast]
pub enum ItemKind<'a> {
    #[doc = " A function or constant item."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
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
    #[doc = " ```rust,ignore"]
    #[doc = " type A = u8;"]
    #[doc = " ```"]
    TyAlias {
        #[doc = " Name of the alias"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `A`"]
        name: PrintContext<'a, origin::GlobalId>,
        #[doc = " Generic arguments and constraints"]
        generics: PrintContext<'a, origin::Generics>,
        #[doc = " Original type"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `u8`"]
        ty: PrintContext<'a, origin::Ty>,
    },
    #[doc = " A type definition (struct or enum)"]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " enum A {B, C}"]
    #[doc = " struct S {f: u8}"]
    #[doc = " ```"]
    Type {
        #[doc = " Name of this type"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `A`, `S`"]
        name: PrintContext<'a, origin::GlobalId>,
        #[doc = " Generic parameters and constraints"]
        generics: PrintContext<'a, origin::Generics>,
        #[doc = " Variants"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `{B, C}`"]
        variants: PrintContext<'a, origin::Vec<origin::Variant>>,
        #[doc = " Is this a struct (or an enum)"]
        is_struct: PrintContext<'a, origin::bool>,
    },
    #[doc = " A trait definition."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " trait T<A> {"]
    #[doc = "     type Assoc;"]
    #[doc = "     fn m(x: Self::Assoc, y: Self) -> A;"]
    #[doc = " }"]
    #[doc = " ```"]
    Trait {
        #[doc = " Name of this trait"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `T`"]
        name: PrintContext<'a, origin::GlobalId>,
        #[doc = " Generic parameters and constraints"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `<A>`"]
        generics: PrintContext<'a, origin::Generics>,
        #[doc = " Items required to implement the trait"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `type Assoc;`, `fn m ...;`"]
        items: PrintContext<'a, origin::Vec<origin::TraitItem>>,
    },
    #[doc = " A trait implementation."]
    #[doc = ""]
    #[doc = " # Example:"]
    #[doc = " ```rust,ignore"]
    #[doc = " impl T<u8> for u16 {"]
    #[doc = "     type Assoc = u32;"]
    #[doc = "     fn m(x: u32, y: u16) -> u8 {"]
    #[doc = "         (x as u8) + (y as u8)"]
    #[doc = "     }"]
    #[doc = " }"]
    #[doc = " ```"]
    Impl {
        #[doc = " Generic arguments and constraints"]
        generics: PrintContext<'a, origin::Generics>,
        #[doc = " The type we implement the trait for"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `u16`"]
        self_ty: PrintContext<'a, origin::Ty>,
        #[doc = " Instantiated trait that is being implemented"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `T<u8>`"]
        of_trait: PrintContext<'a, (origin::GlobalId, origin::Vec<origin::GenericValue>)>,
        #[doc = " Items in this impl"]
        #[doc = ""]
        #[doc = " # Example:"]
        #[doc = " `fn m ...`, `type Assoc ...`"]
        items: PrintContext<'a, origin::Vec<origin::ImplItem>>,
        #[doc = " Implementations of traits required for this impl"]
        parent_bounds: PrintContext<'a, origin::Vec<(origin::ImplExpr, origin::ImplIdent)>>,
        #[doc = " Safe or unsafe"]
        safety: PrintContext<'a, origin::SafetyKind>,
    },
    #[doc = " Internal node introduced by phases, corresponds to an alias to any item."]
    Alias {
        #[doc = " New name"]
        name: PrintContext<'a, origin::GlobalId>,
        #[doc = " Original name"]
        item: PrintContext<'a, origin::GlobalId>,
    },
    #[doc = " A `use` statement"]
    Use {
        #[doc = " Path to used item(s)"]
        path: PrintContext<'a, origin::Vec<origin::String>>,
        #[doc = " Comes from external crate"]
        is_external: PrintContext<'a, origin::bool>,
        #[doc = " Optional `as`"]
        rename: PrintContext<'a, origin::Option<origin::String>>,
    },
    #[doc = " A `Quote` node is inserted by phase TransformHaxLibInline to deal with some `hax_lib` features."]
    #[doc = " For example insertion of verbatim backend code."]
    Quote {
        #[doc = " Content of the quote"]
        quote: PrintContext<'a, origin::Quote>,
        #[doc = " Description of the quote target position"]
        origin: PrintContext<'a, origin::ItemQuoteOrigin>,
    },
    #[doc = " Fallback constructor to carry errors."]
    Error(PrintContext<'a, origin::Diagnostic>),
    #[doc = " Item that is not implemented yet"]
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
#[doc = " Extra variants for [`ExprKind`]."]
#[doc = " This is a resugaring view on [`ExprKind`]."]
#[derive_group_for_ast_base]
pub enum ResugaredExprKind<'a> {
    #[doc = " A constant with applied generics"]
    ConstantApp {
        #[doc = " The constant"]
        constant: PrintContext<'a, origin::GlobalId>,
        #[doc = " The generics"]
        generics: PrintContext<'a, origin::Vec<origin::GenericValue>>,
    },
}
#[doc = " Extra variants for [`PatKind`]."]
#[doc = " This is a resugaring view on [`ExprKind`]."]
#[derive_group_for_ast_base]
pub enum ResugaredPatKind {}
#[doc = " Extra variants for [`TyKind`]."]
#[doc = " This is a resugaring view on [`TyKind`]."]
#[derive_group_for_ast_base]
pub enum ResugaredTyKind {}
#[allow(missing_docs)]
#[doc = r" An owned fragment of the print view: this `enum` can represent any node in the AST."]
#[derive_group_for_ast]
pub enum Fragment<'a> {
    GenericValue(GenericValue<'a>),
    PrimitiveTy(PrimitiveTy<'a>),
    Region(Region),
    Ty(Ty<'a>),
    TyKind(TyKind<'a>),
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
    ResugaredTyKind(ResugaredTyKind),
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
impl<'a> From<TyKind<'a>> for Fragment<'a> {
    fn from(item: TyKind<'a>) -> Self {
        Self::TyKind(item)
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
impl<'a> From<ResugaredTyKind> for Fragment<'a> {
    fn from(item: ResugaredTyKind) -> Self {
        Self::ResugaredTyKind(item)
    }
}
