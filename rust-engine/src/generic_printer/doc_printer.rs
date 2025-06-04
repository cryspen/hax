use super::{print_context::PrintContext, print_view::origin, to_print_view::ToPrintView};
use pretty::{BoxDoc, Doc};
use std::any::Any;

use crate::ast::Attribute;

pub use crate::generic_printer::print_view as destination;

// A represent the type of annotations
pub trait ToDoc<T, A = ()> {
    fn to_doc(&self, x: T) -> Doc<'_, A>;
}

fn print<'a, T, P>(x: PrintContext<'a, T>, p: P) -> Doc<'_>
where
    T: ToPrintView<'a>,
    P: ToDoc<<T as ToPrintView<'a>>::Out>,
{
    p.to_doc(x.to_print_view(x.into()))
}
