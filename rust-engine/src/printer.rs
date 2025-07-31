//! This modules provides types and helper for the printers of hax.

mod allocator;
pub use allocator::Allocator;

use crate::ast;
use pretty::Pretty;
pub mod dynable_visitors {
    //! This modules provides a `dyn`able trait for mapper visitors.
    use super::*;

    /// Helper trait for [`ErasedAstVisitorMut`].
    pub trait ErasedAstVisitorMutHelper<'a, T: ?Sized> {
        /// Visit a value with the visitor.
        fn visit(&mut self, _: &'a mut T);
    }

    macro_rules! derive_erased_ast_visitor_mut {
        ($($ty:ty),*) => {
            /// Erased version of the trait [`AstVisitorMut`].
            pub trait ErasedAstVisitorMut<'a>:
                $(ErasedAstVisitorMutHelper<'a, $ty> + )*
            {}
            $(impl<'a, V: ast::visitors::AstVisitorMut> ErasedAstVisitorMutHelper<'a, $ty> for V {
                fn visit(&mut self, e: &'a mut $ty) {
                    <Self as ast::visitors::AstVisitorMut>::visit(self, e)
                }
            })*
        };
    }

    derive_erased_ast_visitor_mut!(ast::Expr, ast::Item, ast::Ty, ast::Pat);
    impl<'a, V: ast::visitors::AstVisitorMut> ErasedAstVisitorMut<'a> for V {}
}

/// A resugaring is an erased mapper visitor with a name.
/// A resugaring is a *local* transformation on the AST that produces exclusively `ast::resugared` nodes.
/// Any involved or non-local transformation should be a phase, not a resugaring.
pub trait Resugaring: for<'a> dynable_visitors::ErasedAstVisitorMut<'a> {
    /// Get the name of the resugar.
    fn name(&self) -> String;
}

/// A printer defines a list of resugaring phases.
pub trait Printer: Sized {
    /// A list of resugaring phases.
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>>;
}

/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// Helper trait to print AST fragments.
pub trait Print<T>: Printer {
    /// Print a fragment using a backend.
    fn print(self, fragment: &mut T) -> Option<(String, SourceMap)>;
}

macro_rules! derive_print {
    ($($ty:ty),*) => {
        $(
            impl<P: Printer> Print<$ty> for P
            where
                for<'a, 'b> &'b $ty: Pretty<'a, Allocator<Self>, ast::span::Span>,
            {
                fn print(self, fragment: &mut $ty) -> Option<(String, SourceMap)> {
                    for mut reguaring_phase in Self::resugaring_phases() {
                        reguaring_phase.visit(fragment)
                    }
                    let allocator = Allocator::new(self);
                    let doc = fragment.pretty(&allocator).into_doc();
                    let mut mem = Vec::new();
                    doc.render(80, &mut mem).ok()?;
                    Some((str::from_utf8(&mem).ok()?.to_string(), SourceMap))
                }
            }
        )*
    };
}
derive_print!(ast::Expr, ast::Item, ast::Pat, ast::Ty);
