//! Source positions.

use hax_rust_engine_macros::*;

// TODO: implement, interned (statically -- bumpalo or something)
/// Position in the source code
#[derive_group_for_ast]
#[derive(Copy)]
pub struct Span(());

impl From<hax_frontend_exporter::Span> for Span {
    fn from(_span: hax_frontend_exporter::Span) -> Self {
        Self(())
    }
}

impl From<&hax_frontend_exporter::Span> for Span {
    fn from(span: &hax_frontend_exporter::Span) -> Self {
        span.clone().into()
    }
}
