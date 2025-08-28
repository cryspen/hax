//! The "resugaring" phases used by printers.

//! This module defines resugarings instances (see
//! [`hax_rust_engine::ast::Resugaring`] for the definition of a
//! resugaring). Each backend defines its own set of resugaring phases.

use crate::ast::resugared::*;
use crate::ast::visitors::*;
use crate::ast::*;
use crate::printer::*;

/// Makes functions of arity zero into constants.
#[derive(Copy, Clone, Default)]
pub struct FunctionsToConstants;

impl AstVisitorMut for FunctionsToConstants {
    fn enter_item_kind(&mut self, item_kind: &mut ItemKind) {
        let ItemKind::Fn {
            name,
            generics,
            body,
            params,
            safety: SafetyKind::Safe,
        } = item_kind
        else {
            return;
        };
        if !(params.is_empty() && generics.constraints.is_empty() && generics.params.is_empty()) {
            return;
        }
        *item_kind = ItemKind::Resugared(ResugaredItemKind::Constant {
            name: name.clone(),
            body: body.clone(),
        });
    }
}

impl Resugaring for FunctionsToConstants {
    fn name(&self) -> String {
        "functions-to-constants".to_string()
    }
}

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

/// Tuples resugaring. Resugars tuple constructors to the dedicated expression variant [`ResugaredExprKind::Tuple`],
/// and tuple types to the dedicated type variant [`ResugaredTyKind::Tuple`].
pub struct Tuples;

impl AstVisitorMut for Tuples {
    fn enter_expr_kind(&mut self, x: &mut ExprKind) {
        let (constructor, fields) = match x {
            ExprKind::Construct {
                constructor,
                is_record: false,
                is_struct: true,
                base: None,
                fields,
            } => (constructor, &fields[..]),
            ExprKind::GlobalId(constructor) => (constructor, &[][..]),
            _ => return,
        };
        if constructor.is_tuple() {
            let args = fields.iter().map(|(_, e)| e).cloned().collect();
            *x = ExprKind::Resugared(ResugaredExprKind::Tuple(args))
        }
    }
    fn enter_ty_kind(&mut self, x: &mut TyKind) {
        let TyKind::App { head, args } = x else {
            return;
        };
        if head.is_tuple() {
            let Some(args) = args
                .iter()
                .map(GenericValue::expect_ty)
                .collect::<Option<Vec<_>>>()
            else {
                return;
            };
            *x = TyKind::Resugared(ResugaredTyKind::Tuple(args.into_iter().cloned().collect()))
        }
    }
}

impl Resugaring for Tuples {
    fn name(&self) -> String {
        "tuples".to_string()
    }
}
