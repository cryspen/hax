use std::fmt::Debug;

use hax_types::cli_options::Glob;

use crate::ast::identifiers::GlobalId;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;
#[derive(Default, Debug)]
pub struct RenameCore;

/// Stateless visitor
#[setup_error_handling_struct]
#[derive(Default)]
struct RenameCoreVisitor;

impl Phase for RenameCore {
    fn apply(&self, items: &mut Vec<Item>) {
        RenameCoreVisitor::default().visit(items)
    }
}

impl VisitorWithContext for RenameCoreVisitor {
    fn context(&self) -> Context {
        Context::Phase(stringify!(RenameCore).into())
    }
}

const OLD_KRATE_NAME: &str = "core";
const NEW_KRATE_NAME: &str = "core_models";

impl RenameCoreVisitor {
    fn visit_expr_rename(&mut self, expr: &mut Expr) {
        if let ExprKind::GlobalId(global_id) = *expr.kind
            && global_id.krate() == OLD_KRATE_NAME
        {
            *expr.kind = ExprKind::GlobalId(global_id.rename_krate(NEW_KRATE_NAME))
        }
    }
}

impl AstVisitorMut for RenameCoreVisitor {
    setup_error_handling_impl!();

    // fn visit_expr(&mut self, x: &mut Expr) {
    //     self.visit_expr_rename(x)
    // }

    fn enter_expr(&mut self, x: &mut Expr) {
        self.visit_expr_rename(x)
    }

    // fn visit_ty(&mut self, x: &mut Ty) {
    //     if let TyKind::Array { length, .. } = x.kind_mut() {
    //         self.visit_expr_rename(MonadicStatus::Value, length);
    //     };
    // }

    // fn visit_generic_value(&mut self, x: &mut GenericValue) {
    //     if let GenericValue::Expr(expr) = x {
    //         self.visit_expr_rename(MonadicStatus::Value, expr);
    //     };
    // }
}
