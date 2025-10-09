//! A phase rewrites the AST.

use crate::ast::Item;

/// Placeholder trait for phases.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);
}

use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::printer::Print;

#[derive(Clone, Copy, Debug)]
enum DoDslExprKind {
    Statement,
    Expression,
}

fn dsl_expr_kind(expr_kind: &ExprKind) -> DoDslExprKind {
    // TODO: complete that pattern
    if matches!(
        expr_kind,
        ExprKind::If { .. } | ExprKind::Match { .. } | ExprKind::Let { .. }
    ) {
        DoDslExprKind::Statement
    } else {
        DoDslExprKind::Expression
    }
}

impl Default for DoDslExprKind {
    fn default() -> Self {
        Self::Statement
    }
}

#[derive(Default)]
pub struct RejectNotDoLeanDsl;

#[setup_error_handling_struct]
#[derive(Default)]
pub struct RejectNotDoLeanDslVisitor {
    dsl_expr_kind: DoDslExprKind,
}

impl VisitorWithContext for RejectNotDoLeanDslVisitor {
    fn context(&self) -> Context {
        // TODO: give a proper context to this phase
        Context::Import
    }
}

impl AstVisitorMut for RejectNotDoLeanDslVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        use DoDslExprKind::*;
        let previous_dsl_expr_kind = self.dsl_expr_kind;
        self.dsl_expr_kind = match (self.dsl_expr_kind, dsl_expr_kind(&expr.kind)) {
            (Expression, Statement) => {
                self.error(expr.clone(), DiagnosticInfoKind::UnsafeBlock);
                Statement
            }
            (_, kind) => kind,
        };
        self.visit_inner(expr);
        self.dsl_expr_kind = previous_dsl_expr_kind;
    }

    // fn visit_ty(&mut self,x: &mut Ty) {

    // }
}

impl Phase for RejectNotDoLeanDsl {
    fn apply(&self, items: &mut Vec<Item>) {
        RejectNotDoLeanDslVisitor::default().visit(items)
    }
}
