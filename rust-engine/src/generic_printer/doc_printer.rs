use super::{
    print_context::{PrintContext, PrintContextPayload},
    to_print_view::*,
};

use pretty::RcDoc;
use std::any::Any;
use std::rc::Rc;

use super::{print_view, to_print_view};
use crate::ast;

pub use crate::generic_printer::print_view as destination;

pub trait Printer {
    fn resugar_expr(e: ast::Expr) -> Option<super::resugar::ResugaredExprKind>;
}

// A represent the type of annotations
pub trait ToDoc<'a, T> {
    fn to_doc(&self, x: T, p: PrintContextPayload<'a>) -> RcDoc<()>;
}

pub fn print<'a, T, P>(x: PrintContext<'a, T>, p: &'a P) -> RcDoc<'a, ()>
where
    T: ToPrintView<'a>,
    &'a T: Into<ast::node::NodeRef<'a>>,
    P: ToDoc<'a, <T as ToPrintView<'a>>::Out>,
{
    let payload = x.payload.clone();
    p.to_doc(x.value.to_print_view(Some(Rc::new(x.into()))), payload)
}

// impl<'a, P: Printer + ToDoc<'a, print_view::Expr<'a>>> ToDoc<'a, ast::Expr> for P {
//     fn to_doc(&self, x: ast::Expr, p: PrintContextPayload<'a>) -> RcDoc<()> {
//         // TODO Apply resugaring
//         let v: print_view::Expr = (x.to_print_view(Some(Rc::new(x.into()))));
//         self.to_doc(
//             v,
//             PrintContextPayload {
//                 position: "root".to_string(),
//                 parent: None,
//             },
//         )
//     }
// }
