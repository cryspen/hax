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

use crate::{
    ast::{self, span::Span},
    attributes::LinkedItemGraph,
    printer::pretty_ast::ToDocument,
};
use ast::visitors::dyn_compatible;

pub mod pretty_ast;
pub use pretty_ast::PrettyAst;

pub mod render_view;

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
pub trait Printer: Sized + PrettyAst<Span> + Default + HasLinkedItemGraph {
    /// The name of the printer
    const NAME: &'static str = <Self as PrettyAst<Span>>::NAME;

    /// Target page width handed to the `pretty` layout algorithm. Backends
    /// may override this; e.g. the ProVerif backend uses a wider page
    /// because its flattened `a__b__c` identifiers are long, so an 80-column
    /// page would force almost every list to break. Defaults to 80 (matching
    /// the Lean backend).
    const RENDER_WIDTH: usize = 80;
}

/// Getter and setter for `LinkedItemGraph`, useful for printers.
pub trait HasLinkedItemGraph {
    /// Get a reference of the `LinkedItemGraph`.
    fn linked_item_graph(&self) -> &LinkedItemGraph;
    /// Set a `LinkedItemGraph`.
    fn with_linked_item_graph(self, graph: std::rc::Rc<LinkedItemGraph>) -> Self;
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// A `pretty` renderer that, while producing the rendered text exactly as
/// [`pretty::DocBuilder::pretty`] would, also captures the output position
/// `(line, col)` (both 0-based) at which every [`Span`]-annotated sub-document
/// begins. Backends opt in by wrapping the doc nodes they want mapped with
/// [`pretty::DocBuilder::annotate`] (e.g. each top-level item); the resulting
/// `(line, col, span)` list is everything a source map needs.
///
/// The text is byte-identical to the plain `.pretty(width).to_string()` path:
/// the same `pretty::Doc::render` layout algorithm runs, and annotations are
/// zero-width (they never affect layout), so this can be used as a drop-in that
/// additionally yields provenance. Shared here (over the common `A = Span`
/// annotation type) so any backend — ProVerif today, Lean/Rust later — can
/// produce a source map the same way.
#[derive(Default)]
pub struct SpanPositionRenderer {
    /// Accumulated rendered text.
    pub out: String,
    /// Current output line (0-based).
    line: usize,
    /// Current output column (0-based, counted in `char`s).
    col: usize,
    /// Annotation stack: each entry is `(span, already_anchored)`.
    stack: Vec<(Span, bool)>,
    /// Captured `(line, col, span)` anchors, one per annotated region.
    pub positions: Vec<(usize, usize, Span)>,
}

impl SpanPositionRenderer {
    /// Anchor every not-yet-anchored span on the stack to the current output
    /// position (called right before the next chunk of text is written, so a
    /// region maps to the position of its first character).
    fn anchor(&mut self) {
        let (line, col) = (self.line, self.col);
        for entry in self.stack.iter_mut() {
            if !entry.1 {
                self.positions.push((line, col, entry.0));
                entry.1 = true;
            }
        }
    }
}

impl pretty::Render for SpanPositionRenderer {
    type Error = ();

    fn write_str(&mut self, s: &str) -> Result<usize, Self::Error> {
        if s.is_empty() {
            return Ok(0);
        }
        self.anchor();
        for c in s.chars() {
            if c == '\n' {
                self.line += 1;
                self.col = 0;
            } else {
                self.col += 1;
            }
        }
        self.out.push_str(s);
        Ok(s.len())
    }

    fn fail_doc(&self) -> Self::Error {}
}

impl<'a> pretty::RenderAnnotated<'a, Span> for SpanPositionRenderer {
    fn push_annotation(&mut self, span: &'a Span) -> Result<(), Self::Error> {
        self.stack.push((*span, false));
        Ok(())
    }

    fn pop_annotation(&mut self) -> Result<(), Self::Error> {
        // A region that produced no text leaves an un-anchored entry; dropping
        // it here keeps its (stale) span from being anchored to later text.
        self.stack.pop();
        Ok(())
    }
}

/// Render `fragment` with `printer`, returning the text (byte-identical to
/// [`Print::print`]) together with the output `(line, col, span)` of every
/// `Span`-annotated sub-document. See [`SpanPositionRenderer`].
pub fn render_with_span_positions<P: Printer, T>(
    printer: &P,
    fragment: T,
    width: usize,
) -> (String, Vec<(usize, usize, Span)>)
where
    T: ToDocument<P, Span>,
{
    let doc = fragment.to_document(printer).into_doc();
    let mut renderer = SpanPositionRenderer::default();
    // The proverif/Lean/Rust printers never emit `Doc::fail`, so render is
    // infallible; ignore the `Result<(), ()>`.
    let _ = doc.deref().render_raw(width, &mut renderer);
    (renderer.out, renderer.positions)
}

/// Helper trait to print AST fragments.
pub trait Print<T>
where
    for<'a> dyn Resugaring: dyn_compatible::AstVisitableMut<'a, T>,
{
    /// Print a single AST fragment using this backend.
    fn print_returning_fragment(&mut self, fragment: T) -> (String, SourceMap, T)
    where
        T: ToDocument<Self, Span>;

    /// Print a single AST fragment using this backend.
    fn print(&mut self, fragment: T) -> (String, SourceMap)
    where
        T: ToDocument<Self, Span>;
}

impl<P: Printer, T> Print<T> for P
where
    for<'a> dyn Resugaring: dyn_compatible::AstVisitableMut<'a, T>,
{
    fn print_returning_fragment(&mut self, fragment: T) -> (String, SourceMap, T)
    where
        T: ToDocument<Self, Span>,
    {
        let doc_builder = fragment.to_document(self).into_doc();
        (
            doc_builder
                .deref()
                .pretty(<Self as Printer>::RENDER_WIDTH)
                .to_string(),
            SourceMap,
            fragment,
        )
    }

    fn print(&mut self, fragment: T) -> (String, SourceMap)
    where
        T: ToDocument<Self, Span>,
    {
        let (rendered, sourcemap, _) = <Self as Print<_>>::print_returning_fragment(self, fragment);
        (rendered, sourcemap)
    }
}
