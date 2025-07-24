use crate::ast;
use ast::{HasKind, HasSpan};

/// A set of diagnostics a `diag` visitor accumulates.
/// This holds diagnostics temporarly before inlining them in the AST.
#[derive(Default)]
pub struct DiagnosticSet {
    diagnostics: Vec<ast::diagnostics::Diagnostic>,
}

#[inline(always)]
pub(super) fn with_span<T: HasSpan + ?Sized, R>(
    visitor: &mut T,
    span: ast::Span,
    mut f: impl FnMut(&mut T) -> R,
) -> R {
    let previous = visitor.span_mut().clone();
    *visitor.span_mut() = span;
    let result = f(visitor);
    *visitor.span_mut() = previous;
    result
}

pub(super) trait HandleDiagnostics {
    fn handle_diagnostics(&mut self, diagnostic_set: DiagnosticSet);
}

impl HandleDiagnostics for ast::Expr {
    fn handle_diagnostics(&mut self, diagnostic_set: DiagnosticSet) {
        let fragment = Box::new(self.kind().clone().into());
        let DiagnosticSet { diagnostics } = diagnostic_set;

        *self.kind = ast::ExprKind::Error(ast::ErrorNode {
            fragment,
            diagnostics,
        });
    }
}
impl HandleDiagnostics for ast::Pat {
    fn handle_diagnostics(&mut self, diagnostic_set: DiagnosticSet) {
        let fragment = Box::new(self.kind().clone().into());
        let DiagnosticSet { diagnostics } = diagnostic_set;
        *self.kind = ast::PatKind::Error(ast::ErrorNode {
            fragment,
            diagnostics,
        });
    }
}
impl HandleDiagnostics for ast::Item {
    fn handle_diagnostics(&mut self, diagnostic_set: DiagnosticSet) {
        let fragment = Box::new(self.kind().clone().into());
        let DiagnosticSet { diagnostics } = diagnostic_set;
        if !diagnostics.is_empty() {
            self.kind = ast::ItemKind::Error(ast::ErrorNode {
                fragment,
                diagnostics,
            });
        }
    }
}
