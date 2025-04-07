// TODO: implement, interned (statically -- bumpalo or something)
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
