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

use std::{fmt, ops::Deref};

use crate::{
    ast::{self, span::Span},
    attributes::LinkedItemGraph,
    printer::pretty_ast::ToDocument,
};
use ast::visitors::dyn_compatible;
use pretty::RenderAnnotated;

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
}

/// Getter and setter for `LinkedItemGraph`, useful for printers.
pub trait HasLinkedItemGraph {
    /// Get a reference of the `LinkedItemGraph`.
    fn linked_item_graph(&self) -> &LinkedItemGraph;
    /// Set a `LinkedItemGraph`.
    fn with_linked_item_graph(self, graph: std::rc::Rc<LinkedItemGraph>) -> Self;
}

/// Raw source map data collected during rendering.
///
/// Each entry is `(gen_line, gen_col, source_path, src_line, src_col)` where
/// all values are 0-indexed.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct SourceMap {
    /// Mappings as `(gen_line, gen_col, source_path, src_line, src_col)`, all 0-indexed.
    pub raw: Vec<(u32, u32, String, u32, u32)>,
}

impl SourceMap {
    /// Encode the collected mappings into a source map v3
    /// [`hax_types::engine_api::SourceMap`].
    ///
    /// Returns `None` when there are no mappings (e.g. for backends that do
    /// not override [`PrettyAst::annotate_with_span`]).
    pub fn to_engine_sourcemap(
        &self,
        file: &str,
    ) -> Option<hax_types::engine_api::SourceMap> {
        if self.raw.is_empty() {
            return None;
        }

        // Collect unique source paths while preserving insertion order.
        let mut sources: Vec<String> = vec![];
        for (_, _, src, _, _) in &self.raw {
            if !sources.contains(src) {
                sources.push(src.clone());
            }
        }

        // Sort mappings by generated position.
        let mut mappings = self.raw.clone();
        mappings.sort_by_key(|&(gl, gc, _, _, _)| (gl, gc));

        // Encode as source map v3 VLQ.
        let encoded = encode_mappings(&mappings, &sources);

        Some(hax_types::engine_api::SourceMap {
            version: 3,
            file: file.to_string(),
            sourceRoot: String::new(),
            sourcesContent: sources.iter().map(|_| None).collect(),
            sources,
            names: vec![],
            mappings: encoded,
        })
    }
}

// ---------------------------------------------------------------------------
// VLQ / source-map v3 encoding
// ---------------------------------------------------------------------------

const BASE64_CHARS: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Encode a single signed integer as VLQ base64.
fn vlq_encode(value: i64, out: &mut String) {
    // The first group encodes the sign in its lowest bit.
    let mut encoded = if value < 0 {
        ((-value) << 1) | 1
    } else {
        value << 1
    };
    loop {
        let mut digit = encoded & 0x1F; // 5 bits
        encoded >>= 5;
        if encoded > 0 {
            digit |= 0x20; // set continuation bit
        }
        out.push(BASE64_CHARS[digit as usize] as char);
        if encoded == 0 {
            break;
        }
    }
}

/// Encode all mappings into the source map v3 `mappings` string.
fn encode_mappings(
    mappings: &[(u32, u32, String, u32, u32)],
    sources: &[String],
) -> String {
    let mut result = String::new();
    let mut prev_gen_line: u32 = 0;
    let mut prev_gen_col: i64 = 0;
    let mut prev_src_idx: i64 = 0;
    let mut prev_src_line: i64 = 0;
    let mut prev_src_col: i64 = 0;
    let mut first_on_line = true;

    for &(gen_line, gen_col, ref source, src_line, src_col) in mappings {
        // Advance to the correct line with semicolons.
        while prev_gen_line < gen_line {
            result.push(';');
            prev_gen_line += 1;
            prev_gen_col = 0;
            first_on_line = true;
        }

        if !first_on_line {
            result.push(',');
        }
        first_on_line = false;

        let src_idx = sources.iter().position(|s| s == source).unwrap_or(0) as i64;

        // generated column (relative)
        vlq_encode(gen_col as i64 - prev_gen_col, &mut result);
        // source file index (relative)
        vlq_encode(src_idx - prev_src_idx, &mut result);
        // original line (relative)
        vlq_encode(src_line as i64 - prev_src_line, &mut result);
        // original column (relative)
        vlq_encode(src_col as i64 - prev_src_col, &mut result);

        prev_gen_col = gen_col as i64;
        prev_src_idx = src_idx;
        prev_src_line = src_line as i64;
        prev_src_col = src_col as i64;
    }

    result
}

// ---------------------------------------------------------------------------
// SourceMapWriter: a writer that collects span annotations while rendering
// ---------------------------------------------------------------------------

/// A writer implementing [`pretty::RenderAnnotated<Span>`] that both accumulates
/// rendered text and records source-map mappings whenever a [`Span`] annotation
/// is pushed.
#[derive(Default)]
pub struct SourceMapWriter {
    /// The fully rendered output string.
    pub output: String,
    /// 0-indexed current line in the output.
    current_line: u32,
    /// 0-indexed current column in the output.
    current_col: u32,
    /// Collected raw mappings (see [`SourceMap::raw`]).
    pub raw_mappings: Vec<(u32, u32, String, u32, u32)>,
}

impl pretty::Render for SourceMapWriter {
    type Error = fmt::Error;

    fn write_str(&mut self, s: &str) -> Result<usize, fmt::Error> {
        for ch in s.chars() {
            if ch == '\n' {
                self.current_line += 1;
                self.current_col = 0;
            } else {
                self.current_col += 1;
            }
        }
        self.output.push_str(s);
        Ok(s.len())
    }

    fn fail_doc(&self) -> fmt::Error {
        fmt::Error
    }
}

impl<'a> RenderAnnotated<'a, Span> for SourceMapWriter {
    fn push_annotation(&mut self, span: &'a Span) -> Result<(), fmt::Error> {
        if let Some(fe_span) = span.as_frontend_spans().first() {
            // Only record mappings for real source files.
            if fe_span.filename.to_path().is_some() {
                let source = fe_span.filename.to_string();
                self.raw_mappings.push((
                    self.current_line,
                    self.current_col,
                    source,
                    // frontend spans are 1-indexed; source map v3 is 0-indexed
                    fe_span.lo.line.saturating_sub(1) as u32,
                    fe_span.lo.col as u32,
                ));
            }
        }
        Ok(())
    }

    fn pop_annotation(&mut self) -> Result<(), fmt::Error> {
        Ok(())
    }
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
        let mut writer = SourceMapWriter::default();
        doc_builder.deref().render_raw(80, &mut writer).ok();
        let source_map = SourceMap { raw: writer.raw_mappings };
        (writer.output, source_map, fragment)
    }

    fn print(&mut self, fragment: T) -> (String, SourceMap)
    where
        T: ToDocument<Self, Span>,
    {
        let (rendered, sourcemap, _) = <Self as Print<_>>::print_returning_fragment(self, fragment);
        (rendered, sourcemap)
    }
}
