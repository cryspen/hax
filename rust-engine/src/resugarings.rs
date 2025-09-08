//! The "resugaring" phases used by printers.

//! This module defines resugarings instances (see
//! [`hax_rust_engine::ast::Resugaring`] for the definition of a
//! resugaring). Each backend defines its own set of resugaring phases.

use crate::ast::resugared::*;
use crate::ast::visitors::*;
use crate::ast::*;
use crate::printer::*;

/// Rewrite every expression application node [`ExprKind::App`] into a
/// [`ResugaredExprKind::App`]. [`ResugaredExprKind::App`] represent known
/// applications with their arity and matchable names, with a fallback case
/// [`App::Unknown`] for unknown functions.
pub struct FunctionApplications;

impl AstVisitorMut for FunctionApplications {
    fn enter_expr_kind(&mut self, x: &mut ExprKind) {
        let ExprKind::App {
            head,
            args,
            generic_args,
            bounds_impls,
            trait_,
        }: &mut ExprKind = x
        else {
            return;
        };
        *x = ExprKind::Resugared(ResugaredExprKind::FunApp {
            generic_args: generic_args.clone(),
            bounds_impls: bounds_impls.clone(),
            trait_: trait_.clone(),
            app: FunApp::destruct_function_application(head, args.as_slice()),
            head: head.clone(),
        });
    }
}

impl Resugaring for FunctionApplications {
    fn name(&self) -> String {
        "function-applications".to_string()
    }
}
