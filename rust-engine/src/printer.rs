//! This modules provides types and helper for the printers of hax.

mod allocator;
pub use allocator::Allocator;

use crate::{ast, resugarings};
use pretty::{docs, DocAllocator, Pretty};

/// A resugaring is an erased mapper visitor with a name.
/// A resugaring is a *local* transformation on the AST that produces exclusively `ast::resugared` nodes.
/// Any involved or non-local transformation should be a phase, not a resugaring.
pub trait Resugaring: for<'a> ast::visitors::dyn_compatible::AstVisitorMut<'a> {
    /// Get the name of the resugar.
    fn name(&self) -> String;
}

/// A printer defines a list of resugaring phases.
pub trait Printer: Sized {
    /// A list of resugaring phases.
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>>;

    // The header (usually imports of prelude)
    const HEADER: &str;
}

/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// Helper trait to print AST fragments.
pub trait Print<T>: Printer {
    /// Print a fragment using a backend.
    fn print(self, fragment: T) -> Option<(String, SourceMap)>;
}

pub struct File(pub Vec<ast::Item>);

impl<'a, 'b, P: Printer> Pretty<'a, Allocator<P>, ast::span::Span> for &'b File
where
    for <'c> &'c ast::Item: Pretty<'a, Allocator<P>, ast::span::Span>,
{
    fn pretty(
        self,
        allocator: &'a Allocator<P>,
    ) -> pretty::DocBuilder<'a, Allocator<P>, ast::span::Span> {
        docs![
            allocator,
            allocator.intersperse(P::HEADER.lines(), allocator.hardline()),
            allocator.intersperse(&self.0, allocator.hardline().append(allocator.hardline()))
        ]
    }
}

impl<P: Printer> Print<File> for P
where
    for<'a, 'b> &'b File: Pretty<'a, Allocator<Self>, ast::span::Span>,
{
    fn print(self, mut fragment: File) -> Option<(String, SourceMap)> {
        for mut reguaring_phase in Self::resugaring_phases() {
            for item in &mut fragment.0 {
                reguaring_phase.visit(item)
            }
        }
        let allocator = Allocator::new(self);
        let doc = fragment.pretty(&allocator).into_doc();
        let mut mem = Vec::new();
        doc.render(80, &mut mem).ok()?;
        Some((str::from_utf8(&mem).ok()?.to_string(), SourceMap))
    }
}

macro_rules! derive_print {
    ($($ty:ty),*) => {
        $(
            impl<P: Printer> Print<$ty> for P
            where
                for<'a, 'b> &'b $ty: Pretty<'a, Allocator<Self>, ast::span::Span>,
            {
                fn print(self, mut fragment: $ty) -> Option<(String, SourceMap)> {
                    for mut reguaring_phase in Self::resugaring_phases() {
                        reguaring_phase.visit(&mut fragment)
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
