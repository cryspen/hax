//! This module provides a custom [`pretty`] allocator, indexed by a printer,
//! enabling multiple printers to cohexist and to implement the type `Pretty`.

use crate::ast::span::Span;
use pretty::*;

/// A printer-specific [`pretty`] allocator.
pub struct Allocator<Printer> {
    /// The pretty allocator
    allocator: BoxAllocator,
    /// Extra printer-specific context
    pub printer: Printer,
}

impl<'a, P, A: 'a> DocAllocator<'a, A> for Allocator<P> {
    type Doc = <BoxAllocator as DocAllocator<'a, A>>::Doc;

    fn alloc(&'a self, doc: Doc<'a, Self::Doc, A>) -> Self::Doc {
        self.allocator.alloc(doc)
    }

    fn alloc_column_fn(
        &'a self,
        f: impl Fn(usize) -> Self::Doc + 'a,
    ) -> <Self::Doc as DocPtr<'a, A>>::ColumnFn {
        self.allocator.alloc_column_fn(f)
    }

    fn alloc_width_fn(
        &'a self,
        f: impl Fn(isize) -> Self::Doc + 'a,
    ) -> <Self::Doc as DocPtr<'a, A>>::WidthFn {
        self.allocator.alloc_width_fn(f)
    }
}

/// A helper type used to manually implement `Pretty` for types that carry spans.
///
/// By default, we implement the `Pretty` trait for all span-carrying
/// types. These implementations annotate spans in the generated document, allowing
/// source spans to be produced during pretty-printing. However, this default behavior
/// does not provide access to the underlying data, which is sometimes necessary
/// for custom printing logic.
///
/// For example, when printing an item, it's often useful to access its attributes.
/// To support this, the default `Pretty` implementations delegate to `Manual<Item>`,
/// which allows printers to access the inner value directly.
///
/// In practice, calling `expr.pretty(..)` will internally use
/// `Manual(expr).pretty(..)`, enabling more flexible control over printing behavior.
struct Manual<T>(T);

use crate::ast::*;
macro_rules! impl_pretty_kind_meta {
        ($($type:ty),*) => {
            $(impl<'a, 'b, P> Pretty<'a, Allocator<P>, Span> for &'b $type
            where
                Manual<&'b $type>: Pretty<'a, Allocator<P>, Span>,
            {
                fn pretty(self, allocator: &'a Allocator<P>) -> DocBuilder<'a, Allocator<P>, Span> {
                    let doc = Manual(self).pretty(allocator);
                    doc.annotate(self.span())
                }
            })*
        };
    }
impl_pretty_kind_meta!(
    Item,
    Expr,
    Pat,
    Guard,
    Arm,
    ImplItem,
    TraitItem,
    GenericParam,
    Attribute
);
