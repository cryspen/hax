//! The "resugaring" phases used by printers.

//! This module defines resugarings instances (see
//! [`hax_rust_engine::ast::Resugaring`] for the definition of a
//! resugaring). Each backend defines its own set of resugaring phases.

use crate::ast::identifiers::global_id::DefId;
use crate::ast::resugared::*;
use crate::ast::visitors::*;
use crate::ast::*;
use crate::printer::*;
use std::collections::HashSet;

/// Binop resugaring. Used to identify expressions of the form `(f e1 e2)` where
/// `f` is a known identifier.
pub struct BinOp {
    /// Stores a set of identifiers that should be resugared as binary
    /// operations. Usually, those identifiers come from the hax encoding. Each
    /// backend can select its own set of identifiers Typically, if the backend
    /// has a special support for addition, `known_ops` will contain
    /// `hax::machine::int::add`
    pub known_ops: HashSet<DefId>,
}

impl BinOp {
    /// Adds a new binary operation from a list of (hax-introduced) names
    pub fn new(known_ops: &[DefId]) -> Self {
        Self {
            known_ops: HashSet::from_iter(known_ops.iter().cloned()),
        }
    }
}

impl AstVisitorMut for BinOp {
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
        let ExprKind::GlobalId(id) = &*head.kind else {
            return;
        };
        let [lhs, rhs] = &args[..] else { return };
        if self.known_ops.iter().any(|defid| id == defid) {
            *x = ExprKind::Resugared(ResugaredExprKind::BinOp {
                op: id.clone(),
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                generic_args: generic_args.clone(),
                bounds_impls: bounds_impls.clone(),
                trait_: trait_.clone(),
            });
        }
    }
}

impl Resugaring for BinOp {
    fn name(&self) -> String {
        "binop".to_string()
    }
}

/// Errors resugaring. Transforms error nodes into applications
/// of the `hax_error` function. This is actually a desugaring
/// but it is useful at the same time as the resugarings so we
/// keep it here.
pub struct Errors;

impl AstVisitorMut for Errors {
    fn enter_expr(&mut self, x: &mut Expr) {
        if let ExprKind::Error(ErrorNode { fragment, .. }) = x.kind() {
            let error_fn = identifiers::global_id::ConcreteId::from_def_id(
                crate::names::rust_primitives::hax::Failure(),
            )
            .into_concrete();
            let head = Expr {
                kind: Box::new(ExprKind::GlobalId(error_fn)),
                ty: x.ty.clone(),
                meta: x.meta.clone(),
            };
            let args = vec![
                ExprKind::Literal(literals::Literal::String(crate::symbol::Symbol::new(
                    format!("{:?}", fragment),
                )))
                .into_expr(x.meta.span.clone(), x.ty.clone(), Vec::new()),
            ];
            *x.kind = ExprKind::App {
                head,
                args,
                generic_args: Vec::new(),
                bounds_impls: Vec::new(),
                trait_: None,
            };
        }
    }
}

impl Resugaring for Errors {
    fn name(&self) -> String {
        "errors".to_string()
    }
}
