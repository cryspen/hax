//! Provides the trait [`ToPrintView`] and implementations for this trait.
#![allow(unused_qualifications)]

use super::{
    print_context::{ParentPrintContext, PrintContext, PrintContextPayload},
    print_view::origin,
};
use crate::ast::Attribute;
use crate::generic_printer::print_view as destination;

/// Shallow convert an AST fragment into its PrintView equivalent. This trait
/// also provides a type-level map from every AST datatype to its own PrintView
/// equivalent, thanks to the associated type `Out`.
///
/// Every datatype of our AST should implement this trait. Those implementations
/// are generated automatically in `generated/to_print_view.rs`.
pub trait ToPrintView<'a> {
    /// The corresponding PrintView type.
    ///
    /// For example, for [`crate::ast::ExprKind`], this is [`crate::generic_printer::print_view::ExprKind`].
    type Viewed;
    /// Transform self into it's viewed counterpart.
    fn to_print_view(
        &'a self,
        context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Viewed;
}

include!("generated/to_print_view.rs");
