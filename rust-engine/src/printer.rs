//! Printer infrastructure: allocators, traits, and the printing pipeline.
//!
//! This module contains the common plumbing that backends and printers rely on
//! to turn AST values into formatted text:
//! - [`Allocator`]: a thin wrapper around the `pretty` crate's allocator,
//!   parameterized by the backend, used to produce [`pretty::Doc`] nodes.
//! - [`PrettyAst`]: the trait that printers implement to provide per-type
//!   formatting of Hax AST nodes (re-exported from [`pretty_ast`]).
//! - The resugaring pipeline: a sequence of local AST rewrites that make
//!   emitted code idiomatic for the target language before pretty-printing.

use std::ops::Deref;

use crate::ast::{self, span::Span};
use ast::visitors::dyn_compatible;
use pretty::Pretty;

pub mod pretty_ast;
pub use pretty_ast::PrettyAst;

pub mod render_view;

/// Implements `pretty::DocAllocator<'a, A>` for a local types
/// that already implement `HasAllocator<'a, A>`.
///
/// Usage:
///   impl_doc_allocator_for!(MyType);
///
/// Notes:
/// - Types must be local to your crate (orphan rule).
#[macro_export]
macro_rules! impl_doc_allocator_for {
    ($ty:ty) => {
        impl<'a, A: 'a> ::pretty::DocAllocator<'a, A> for $ty {
            type Doc = pretty::BoxDoc<'a, A>;

            fn alloc(&'a self, doc: ::pretty::Doc<'a, Self::Doc, A>) -> Self::Doc {
                pretty::BoxAllocator.alloc(doc)
            }

            fn alloc_column_fn(
                &'a self,
                f: impl Fn(usize) -> Self::Doc + 'a,
            ) -> <Self::Doc as ::pretty::DocPtr<'a, A>>::ColumnFn {
                pretty::BoxAllocator.alloc_column_fn(f)
            }

            fn alloc_width_fn(
                &'a self,
                f: impl Fn(isize) -> Self::Doc + 'a,
            ) -> <Self::Doc as ::pretty::DocPtr<'a, A>>::WidthFn {
                pretty::BoxAllocator.alloc_width_fn(f)
            }
        }
    };
}
pub use impl_doc_allocator_for;

/// A resugaring is an erased mapper visitor with a name.
/// A resugaring is a *local* transformation on the AST that produces exclusively `ast::resugared` nodes.
/// Any involved or non-local transformation should be a phase, not a resugaring.
///
/// Backends may provide **multiple resugaring phases** to incrementally refine
/// the tree into something idiomatic for the target language (e.g., desugaring
/// pattern sugar into a more uniform core, then resugaring back into target
/// idioms). Each phase mutates the AST in place and should be small, focused,
/// and easy to test.
///
/// If you add a new phase, make sure it appears in the backend’s
/// `resugaring_phases()` list in the correct order.
pub trait Resugaring: for<'a> dyn_compatible::AstVisitorMut<'a> {
    /// Get the name of the resugar.
    fn name(&self) -> String;
}

/// A printer defines a list of resugaring phases.
pub trait Printer: Sized + for<'a, 'b> PrettyAst<'a, 'b, Span> + Default {
    /// A list of resugaring phases.
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>>;
    /// The name of the printer
    const NAME: &'static str;
}

/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// Helper trait to print AST fragments.
pub trait Print<T>: Printer {
    /// Print a single AST fragment using this backend.
    fn print(&self, mut fragment: T) -> (String, SourceMap)
    where
        for<'a, 'b> &'b T: Pretty<'a, Self, Span>,
        // The following node is equivalent to "T is an AST node"
        for<'a> dyn Resugaring: dyn_compatible::AstVisitableMut<'a, T>,
    {
        for mut reguaring_phase in Self::resugaring_phases() {
            reguaring_phase.visit(&mut fragment)
        }
        let doc_builder = fragment.pretty(self).into_doc();
        (doc_builder.deref().pretty(80).to_string(), SourceMap)
    }
}
impl<P: Printer, T> Print<T> for P {}
