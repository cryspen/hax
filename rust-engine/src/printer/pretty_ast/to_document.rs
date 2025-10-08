use pretty::{BoxAllocator, DocAllocator};
use std::ops::Deref as _;

/// A convenience alias tying the document builder to the global
/// [`pretty::BoxAllocator`].
pub type DocBuilder<A> = pretty::DocBuilder<'static, BoxAllocator, A>;

/// Convert a value into a document by-value.
///
/// Implementations typically delegate to [`ToDocument`] after adjusting the
/// input ownership (e.g., cloning or borrowing). It allows helpers to accept
/// either borrowed or owned values transparently.
pub trait ToDocumentOwned<P, A> {
    /// Produce a document using the provided printer.
    fn to_document_owned(self, printer: &P) -> DocBuilder<A>;
}

impl<'a, P, A, T: ToDocument<P, A>> ToDocumentOwned<P, A> for &'a T {
    fn to_document_owned(self, printer: &P) -> DocBuilder<A> {
        self.to_document(printer)
    }
}

impl<P, A> ToDocumentOwned<P, A> for DocBuilder<A> {
    fn to_document_owned(self, _printer: &P) -> DocBuilder<A> {
        self
    }
}
impl<P, A> ToDocumentOwned<P, A> for &str {
    fn to_document_owned(self, _printer: &P) -> DocBuilder<A> {
        DocAllocator::as_string(&BoxAllocator, self)
    }
}
impl<P, A> ToDocumentOwned<P, A> for String {
    fn to_document_owned(self, _printer: &P) -> DocBuilder<A> {
        DocAllocator::as_string(&BoxAllocator, self)
    }
}
impl<P, A> ToDocumentOwned<P, A> for Option<&str> {
    fn to_document_owned(self, printer: &P) -> DocBuilder<A> {
        self.map(|s| s.to_document_owned(printer))
            .unwrap_or_else(|| DocAllocator::nil(&BoxAllocator))
    }
}

/// Convert a value into a document using the supplied printer.
///
/// This is the primary trait invoked throughout the pretty-printing pipeline;
/// it mirrors [`pretty::Pretty::pretty`] while giving access to printer-specific
/// context.
pub trait ToDocument<P, A> {
    /// Produce a document using the provided printer reference.
    fn to_document(&self, printer: &P) -> DocBuilder<A>;
}

impl<A, P, T: ToDocument<P, A>> ToDocument<P, A> for Box<T> {
    fn to_document(&self, printer: &P) -> DocBuilder<A> {
        self.deref().to_document(printer)
    }
}
impl<A, P, T: ToDocument<P, A>> ToDocument<P, A> for Option<T> {
    fn to_document(&self, printer: &P) -> DocBuilder<A> {
        self.as_ref()
            .map(|value| value.to_document(printer))
            .unwrap_or_else(|| DocAllocator::nil(&BoxAllocator))
    }
}
impl<A, P> ToDocument<P, A> for String {
    fn to_document(&self, _printer: &P) -> DocBuilder<A> {
        DocAllocator::as_string(&BoxAllocator, self)
    }
}
impl<A: Clone, P> ToDocument<P, A> for DocBuilder<A> {
    #[inline(always)]
    fn to_document(&self, _printer: &P) -> DocBuilder<A> {
        self.clone()
    }
}
impl<'a, A: Clone, P, T> ToDocument<P, A> for &'a T
where
    T: ToDocument<P, A>,
{
    #[inline(always)]
    fn to_document(&self, printer: &P) -> DocBuilder<A> {
        (*self).to_document(printer)
    }
}
