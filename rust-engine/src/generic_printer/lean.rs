use crate::ast::{node::NodeRef, Literal};

use super::{doc_printer::*, print_context::*, print_view::*, to_print_view::*};
use pretty::{BoxDoc, RcDoc};
use std::any::Any;

use crate::ast;

pub struct LeanPrinter;

impl super::doc_printer::Printer for LeanPrinter {
    fn resugar_expr(e: crate::ast::Expr) -> Option<super::resugar::ResugaredExprKind> {
        None
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, PrimitiveTy<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: PrimitiveTy<'a>,
        _context: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<()> {
        match x {
            PrimitiveTy::Bool => todo!(),
            PrimitiveTy::Int(print_context) => todo!(),
            PrimitiveTy::Float(print_context) => todo!(),
            PrimitiveTy::Char => todo!(),
            PrimitiveTy::Str => todo!(),
        }
    }
}

// impl<'a> ToDoc<'a, Box<T>>

impl<'a: 'p, 'p> ToDoc<'a, 'p, Expr<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: Expr<'a>,
        _context: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<'p, ()> {
        let value: &ast::ExprKind = &*x.kind.value;
        super::doc_printer::print(
            PrintContext {
                value: value,
                payload: x.kind.payload,
            },
            self,
        )
    }
}

impl<'a> ToPrintView<'a> for Literal {
    type Out = Self;
    fn to_print_view(
        &'a self,
        _parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        self.clone()
    }
}

impl<'a> Into<NodeRef<'a>> for &Literal {
    fn into(self) -> NodeRef<'a> {
        NodeRef::Literal
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, ExprKind<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: ExprKind<'a>,
        p: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<'p, ()> {
        match x {
            ExprKind::If {
                condition,
                then,
                else_,
            } => match else_.value {
                Some(else_branch) => RcDoc::text("if ")
                    .append(super::doc_printer::print(condition, self))
                    .append(RcDoc::text(" then "))
                    .append(super::doc_printer::print(then, self))
                    .append(RcDoc::text(" else "))
                    .append(super::doc_printer::print(
                        PrintContext {
                            value: else_branch,
                            payload: else_.payload,
                        },
                        self,
                    )),
                None => todo!(),
            },
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => todo!(),
            ExprKind::Literal(lit) => super::doc_printer::print(lit, self),
            ExprKind::Array(print_context) => todo!(),
            ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            } => todo!(),
            ExprKind::Match { scrutinee, arms } => todo!(),
            ExprKind::Tuple(print_context) => todo!(),
            ExprKind::Borrow { mutable, inner } => todo!(),
            ExprKind::AddressOf { mutability, inner } => todo!(),
            ExprKind::Deref(print_context) => todo!(),
            ExprKind::Let { lhs, rhs, body } => todo!(),
            ExprKind::GlobalId(print_context) => todo!(),
            ExprKind::LocalId(print_context) => todo!(),
            ExprKind::Ascription { e, ty } => todo!(),
            ExprKind::Assign { lhs, value } => todo!(),
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => todo!(),
            ExprKind::Break { value, label } => todo!(),
            ExprKind::Return { value } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => todo!(),
            ExprKind::Quote { contents } => todo!(),
            ExprKind::Error(print_context) => todo!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Literal> for LeanPrinter {
    fn to_doc(&self, x: Literal, p: super::print_context::PrintContextPayload<'a>) -> RcDoc<()> {
        match x {
            Literal::String(symbol) => todo!(),
            Literal::Char(_) => todo!(),
            Literal::Bool(true) => RcDoc::text("true"),
            Literal::Bool(false) => RcDoc::text("false"),
            Literal::Int {
                value,
                negative,
                kind,
            } => todo!(),
            Literal::Float {
                value,
                negative,
                kind,
            } => todo!(),
        }
    }
}

#[test]
fn lit_test() {
    let ty = ast::Ty::RawPointer;
    let span = ast::Span(());
    let meta = ast::Metadata {
        span,
        attributes: vec![],
    };
    let expr_false = ast::Expr {
        ty: ty.clone(),
        kind: Box::new(ast::ExprKind::Literal(Literal::Bool(false))),
        meta: meta.clone(),
    };
    let expr_true = ast::Expr {
        ty: ty.clone(),
        kind: Box::new(ast::ExprKind::Literal(Literal::Bool(true))),
        meta: meta.clone(),
    };

    let expr_if = ast::Expr {
        ty,
        kind: Box::new(ast::ExprKind::If {
            condition: expr_true.clone(),
            then: expr_true.clone(),
            else_: Some(expr_false.clone()),
        }),
        meta: meta.clone(),
    };

    let ast = expr_if;
    let doc = LeanPrinter.to_doc(
        ast.to_print_view(None),
        PrintContextPayload {
            position: "root".into(),
            parent: None,
        },
    );
    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    println!("{}", String::from_utf8(w).unwrap());
}
