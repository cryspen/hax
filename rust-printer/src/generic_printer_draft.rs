use crate::ast;

pub use ast::diagnostics::Diagnostic;
pub use ast::identifiers::*;
pub use ast::literals::*;
pub use ast::node::Node;
pub use ast::span::Span;
use std::any::Any;

#[allow(non_camel_case_types)]
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

pub struct Value<'a, T> {
    pub value: &'a T,
    pub position: AstPosition,
    pub parent: Box<Value<'a, Box<dyn Any>>>,
    pub span: Span,
}

pub enum ExprKind<'a> {
    If {
        condition: Value<'a, ast::Expr>,
        then: Value<'a, ast::Expr>,
        else_: Value<'a, ast::Expr>,
    },

    App {
        head: Value<'a, ast::Expr>,
        args: Vec<Value<'a, ast::Expr>>,
        generic_args: Vec<Value<'a, ast::GenericValue>>,
        bounds_impls: Vec<Value<'a, ast::ImplExpr>>,
        trait_: Option<(Value<'a, ast::ImplExpr>, Vec<Value<'a, ast::GenericValue>>)>,
    },
}
