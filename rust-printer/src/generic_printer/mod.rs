mod origin {
    pub use crate::ast::*;
    pub use {bool, Box, Option, String, Vec};

    pub use diagnostics::Diagnostic;
    pub use identifiers::*;
    pub use literals::*;
    pub use node::Node;
    pub use span::Span;
}

trait Resugar {
    type ExprKind;
    fn desugar_expr(&self, expr: origin::Expr) -> Self::ExprKind;
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum AstPosition {
    ExprKind_If_condition,
    ExprKind_If_then,
    ExprKind_If_else_,
    ExprKind_App_head,
    ExprKind_App_args(usize),
    ExprKind_App_generic_args(usize),
    ExprKind_App_bound_impls(usize),
    ExprKind_App_trait_0,
    ExprKind_App_trait_1(usize),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Value<'a, T> {
    pub value: &'a T,
    pub position: AstPosition,
    // pub parent: Box<Value<'a, Box<dyn Any>>>,
    pub span: origin::Span,
}

include!("generated.rs");

mod hello {
    use std::marker::PhantomData;

    use super::Value;

    trait Types {
        type Expr;
        type ExprExt;
    }
    enum Expr<T: Types = ()> {
        If {
            head: Box<T::Expr>,
            then: Box<T::Expr>,
            else_: Box<T::Expr>,
        },
        App {
            head: Box<T::Expr>,
            args: Vec<Box<T::Expr>>,
        },
        Name(String),
        Extension(T::ExprExt),
    }
    impl Types for () {
        type Expr = Expr<()>;
        type ExprExt = ();
    }

    type Doc = ();
    trait Printer {
        fn expr<'a>(expr: Expr<Desugared<'a>>) -> Doc;
    }

    struct TypesWithValue {}

    impl<'a> Into<Expr<Desugared<'a>>> for Expr {
        fn into(self) -> Expr<Desugared<'a>> {
            todo!()
        }
    }

    struct Desugared<'a>(PhantomData<&'a ()>);
    impl<'a> Types for Desugared<'a> {
        type Expr = Value<'a, <() as Types>::Expr>;
        type ExprExt = DesugaredExpr<Desugared<'a>>;
    }
    enum DesugaredExpr<T: Types> {
        Projection(String, T::Expr),
    }
}
