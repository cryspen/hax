//! Source positions.

use hax_rust_engine_macros::*;

/// Creates a fresh identifier for a span.
fn fresh_id() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static CURRENT_ID: AtomicUsize = AtomicUsize::new(0);
    CURRENT_ID.fetch_add(1, Ordering::Relaxed)
}

/// Position of a Rust source
#[derive_group_for_ast]
pub struct Span {
    /// A vector of spans as defined by the frontend.
    /// This is useful for supporting in a trivial way union of spans.
    pub data: Vec<hax_frontend_exporter::Span>,
    /// A unique identifier. Since we store spans almost for every node of the
    /// AST, having a unique identifier for spans gives us a fine-grained way of
    /// refering to sub-nodes in debugging context. This id is indeed mostly
    /// used by the web debugger.
    id: usize,
    /// A reference to the item in which this span lives. This information is
    /// used for debugging and profiling purposes, e.g. for `cargo hax into
    /// --stats backend`.
    owner_hint: Option<Interned<hax_frontend_exporter::DefId>>,
}

impl Span {
    /// Creates a dummy span.
    pub fn dummy() -> Self {
        let lo: hax_frontend_exporter::Loc = hax_frontend_exporter::Loc { line: 0, col: 0 };
        let hi = lo.clone();
        Span {
            data: vec![hax_frontend_exporter::Span {
                lo,
                hi,
                filename: hax_frontend_exporter::FileName::Custom("dumny".into()),
                rust_span_data: None,
            }],
            id: 0,
            owner_hint: None,
        }
    }
}

use crate::interning::{Internable, Interned, InterningTable};
impl Internable for hax_frontend_exporter::DefId {
    fn interning_table() -> &'static std::sync::Mutex<InterningTable<Self>> {
        use std::sync::{LazyLock, Mutex};
        static TABLE: LazyLock<Mutex<InterningTable<hax_frontend_exporter::DefId>>> =
            LazyLock::new(|| Mutex::new(InterningTable::default()));
        &TABLE
    }
}

impl Span {
    /// Creates a [`Span`] given information from the hax exporter.
    pub fn from_exporter(
        span: hax_frontend_exporter::Span,
        owner_hint: Option<&hax_frontend_exporter::DefId>,
    ) -> Self {
        Self {
            data: vec![span],
            id: fresh_id(),
            owner_hint: owner_hint.map(Interned::intern),
        }
    }
}
