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
pub trait ToDoc<'a: 'p, 'p, T> {
    fn to_doc(&'p self, x: T, p: PrintContextPayload<'a>) -> RcDoc<'p, ()>;
}

pub fn print<'a: 'p, 'p, T, P>(x: PrintContext<'a, T>, p: &'p P) -> RcDoc<'p, ()>
where
    T: ToPrintView<'a>,
    &'a T: Into<ast::node::NodeRef<'a>>,
    P: ToDoc<'a, 'p, <T as ToPrintView<'a>>::Out>,
{
    let payload = x.payload.clone();
    p.to_doc(x.value.to_print_view(Some(Rc::new(x.into()))), payload)
}
