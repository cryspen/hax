//! Source positions.

use hax_rust_engine_macros::*;

/// Creates a fresh identifier for a span.
fn fresh_id() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static CURRENT_ID: AtomicUsize = AtomicUsize::new(0);
    CURRENT_ID.fetch_add(1, Ordering::Relaxed)
}

/// Identifier used to track the origin Rust item of a span
#[derive_group_for_ast]
pub struct OwnerId(usize);

/// Position of a Rust source
#[derive_group_for_ast]
pub struct Span {
    /// A vector of spans as defined by the frontend.
    /// This is useful for supporting in a trivial way union of spans.
    data: Vec<hax_frontend_exporter::Span>,
    /// A unique identifier. Since we store spans almost for every node of the
    /// AST, having a unique identifier for spans gives us a fine-grained way of
    /// refering to sub-nodes in debugging context. This id is indeed mostly
    /// used by the web debugger.
    id: usize,
    /// A reference to the item in which this span lives. This information is
    /// used for debugging and profiling purposes, e.g. for `cargo hax into
    /// --stats backend`.
    owner_hint: Option<OwnerId>,
}

impl From<hax_frontend_exporter::Span> for Span {
    fn from(span: hax_frontend_exporter::Span) -> Self {
        Self {
            data: vec![span],
            id: fresh_id(),
            owner_hint: None, // TODO: this will be defined properly while addressing issue #1524
        }
    }
}

impl From<&hax_frontend_exporter::Span> for Span {
    fn from(span: &hax_frontend_exporter::Span) -> Self {
        span.clone().into()
    }
}
