pub mod identifiers;
pub mod literals;
pub mod span;

use crate::symbol::Symbol;

pub use identifiers::*;
pub use literals::*;
pub use span::Span;

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum GenericValue {
    Ty(Ty),
    Expr(Expr),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PrimitiveTy {
    Bool,
    Int(IntKind),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Ty {
    Primitive(PrimitiveTy),
    Tuple(Vec<Ty>),
    App {
        head: GlobalId,
        args: Vec<GenericValue>,
    },
    Arrow {
        inputs: Vec<Ty>,
        output: Box<Ty>,
    },
    Ref {
        inner: Box<Ty>,
        mutable: bool,
    },
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Metadata {
    pub span: Span,
    pub attrs: Attributes,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Expr {
    pub kind: Box<ExprKind>,
    pub ty: Ty,
    pub meta: Metadata,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Pat {
    pub kind: PatKind,
    pub ty: Ty,
    pub meta: Metadata,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum BorrowKind {
    Shared,
    Unique,
    Mut,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum BindingMode {
    ByValue,
    ByRef(BorrowKind),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PatKind {
    Wild,
    Binding {
        mutable: bool,
        var: LocalIdent,
        mode: BindingMode,
    },
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ExprKind {
    If {
        condition: Expr,
        then_: Expr,
        else_: Option<Expr>,
    },
    App {
        head: Expr,
        args: Vec<Expr>,
        // TODO
    },
    Literal(Literal),
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    Borrow {
        mutable: bool,
        inner: Expr,
    },
    Deref(Expr),
    Let {
        lhs: Pat,
        rhs: Expr,
        body: Expr,
    },
    GlobalId(GlobalId),
    LocalId(LocalIdent),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Generics;
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum SafetyKind {
    Safe,
    Unsafe,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Attribute;

pub type Attributes = Vec<Attribute>;

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct SpannedTy {
    pub span: Span,
    pub ty: Ty,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Param {
    pub pat: Pat,
    pub ty: SpannedTy,
    pub attributes: Attributes,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ItemKind {
    Fn {
        name: GlobalId,
        generics: Generics,
        body: Expr,
        params: Vec<Param>,
        safety: SafetyKind,
    },
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]

pub struct Item {
    pub ident: GlobalId,
    pub kind: ItemKind,
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
