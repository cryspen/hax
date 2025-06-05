use crate::ast::Literal;

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

impl<'a> ToDoc<'a, PrimitiveTy<'a>> for LeanPrinter {
    fn to_doc(
        &self,
        x: PrimitiveTy<'a>,
        p: super::print_context::PrintContextPayload<'a>,
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

impl<'a> ToDoc<'a, Expr<'a>> for LeanPrinter {
    //
    // impl<'a, T: OpenPrintContext<'a>> OpenPrintContext<'a> for Box<T> {
    //     type Inner = Box<T::Inner>;
    //     fn open(ctx: PrintContext<'a, Self>) -> Self::Inner {
    //         let value: &'a T = &*ctx.value;
    //         Box::new(
    //             PrintContext {
    //                 value,
    //                 payload: ctx.payload.clone(),
    //             }
    //             .open(),
    //         )
    //     }
    // }

    fn to_doc(&self, x: Expr<'a>, p: super::print_context::PrintContextPayload<'a>) -> RcDoc<()> {
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

impl<'a> ToDoc<'a, ExprKind<'a>> for LeanPrinter {
    fn to_doc(
        &self,
        x: ExprKind<'a>,
        p: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<()> {
        match x {
            ExprKind::If {
                condition,
                then,
                else_,
            } => super::doc_printer::print(then, self),
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => todo!(),
            ExprKind::Literal(print_context) => todo!(),
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

impl<'a> ToDoc<'a, Literal> for LeanPrinter {
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
    let ast = Literal::Bool(true);
    let doc = LeanPrinter.to_doc(
        ast,
        PrintContextPayload {
            position: "root".into(),
            parent: None,
        },
    );
    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    println!("{}", String::from_utf8(w).unwrap());
}
