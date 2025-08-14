//! This modules provides types and helper for the printers of hax.

mod allocator;
pub use allocator::Allocator;

use crate::ast;
use ast::visitors::dyn_compatible;
use pretty::Pretty;

/// A resugaring is an erased mapper visitor with a name.
/// A resugaring is a *local* transformation on the AST that produces exclusively `ast::resugared` nodes.
/// Any involved or non-local transformation should be a phase, not a resugaring.
pub trait Resugaring: for<'a> dyn_compatible::AstVisitorMut<'a> {
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

impl<P: Printer, T: ast::visitors::AstVisitorMut + ast::visitors::AstVisitableInfallible> Print<T>
    for P
where
    for<'a, 'b> &'b T: Pretty<'a, Allocator<Self>, ast::span::Span>,
    // The following node is equivalent to "T is an AST node"
    for<'a> dyn Resugaring: dyn_compatible::AstVisitableMut<'a, T>,
{
    fn print(self, fragment: &mut T) -> Option<(String, SourceMap)> {
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
