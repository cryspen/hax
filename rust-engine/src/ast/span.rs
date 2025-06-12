//! Source positions.

use hax_rust_engine_macros::*;
use std::sync::atomic::{AtomicUsize, Ordering};

static CURRENT_ID: AtomicUsize = AtomicUsize::new(0);

fn new_id() -> usize {
    CURRENT_ID.fetch_add(1, Ordering::Relaxed)
}

/// Id for the origin item of a span
#[derive_group_for_ast]
pub struct OwnerId(usize);

/// Position in the source code
#[derive_group_for_ast]
pub struct Span {
    data: Vec<hax_frontend_exporter::Span>,
    id: usize,
    owner_hint: Option<OwnerId>,
}

impl From<hax_frontend_exporter::Span> for Span {
    fn from(span: hax_frontend_exporter::Span) -> Self {
        Self {
            data: vec![span],
            id: new_id(),
            owner_hint: None, // TODO: Have something there when we implement the importer
        }
    }
}

impl From<&hax_frontend_exporter::Span> for Span {
    fn from(span: &hax_frontend_exporter::Span) -> Self {
        span.clone().into()
    }
}
