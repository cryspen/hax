use super::{
    doc_print::ToDoc, print_context::PrintContext, print_view::*, to_print_view::ToPrintAst,
};
use pretty::{BoxDoc, Doc};
use std::any::Any;

pub struct LeanPrinter;

impl ToDoc<LeanPrinter> for PrimitiveTy {
    fn to_doc(&self, _printer: &LeanPrinter) -> Doc<'_, ()> {
        match self {
            PrimitiveTy::Bool => todo!(),
            PrimitiveTy::Int(print_context) => todo!(),
        }
    }
}
impl ToDoc<LeanPrinter> for ExprKind {
    fn to_doc(&self, _printer: &LeanPrinter) -> Doc<'_, ()> {
        match self {
            ExprKind::If {
                condition,
                then,
                else_,
            } => match else_ {
                Some(else_branch) => doc![
                    "if ",
                    condition.to_doc(p),
                    " then ",
                    then.to_doc(p),
                    " else ",
                    else_branch.to_doc(p)
                ],
                None => todo!(),
            },
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
            ExprKind::Deref(print_context) => todo!(),
            ExprKind::Let { lhs, rhs, body } => todo!(),
            ExprKind::GlobalId(print_context) => todo!(),
            ExprKind::LocalId(print_context) => todo!(),
            ExprKind::Error(print_context) => todo!(),
            ExprKind::Ascription { e, ty } => todo!(),
            ExprKind::Assign { lhs, value } => todo!(),
            ExprKind::Loop { body, label } => todo!(),
            ExprKind::Break { value, label } => todo!(),
            ExprKind::Return { value } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => todo!(),
        }
    }
}
