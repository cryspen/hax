//! A phase rewrites the AST.

/// Placeholder trait for phases.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);
}

use std::collections::HashSet;
use std::fmt::Debug;

use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::printer::Print;

#[derive(Default, Debug)]
pub struct ExplicitMonadic;

#[setup_error_handling_struct]
#[derive(Default)]
pub struct ExplicitMonadicVisitor;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum MonadicStatus {
    Computation,
    Value,
}

impl Default for MonadicStatus {
    fn default() -> Self {
        Self::Computation
    }
}

impl Phase for ExplicitMonadic {
    fn apply(&self, items: &mut Vec<Item>) {
        ExplicitMonadicVisitor::default().visit(items)
    }
}

impl ExplicitMonadicVisitor {
    fn coerce(&mut self, expr: &mut Expr, from: MonadicStatus, to: MonadicStatus) {
        if from == to {
            return;
        }
        let inner = expr.clone();
        match to {
            MonadicStatus::Computation => {
                // TODO: add helper for constructing function calls
                expr.kind = Box::new(ExprKind::App {
                    head: Expr {
                        kind: Box::new(ExprKind::GlobalId(
                            crate::names::rust_primitives::hax::explicit_monadic::pure,
                        )),
                        ty: Ty(Box::new(TyKind::Arrow {
                            inputs: vec![inner.ty.clone()],
                            output: inner.ty.clone(),
                        })),
                        meta: Metadata {
                            span: expr.meta.span.clone(),
                            attributes: vec![],
                        },
                    },
                    args: vec![expr.clone()],
                    generic_args: vec![],
                    bounds_impls: vec![],
                    trait_: None,
                });
            }
            MonadicStatus::Value => {
                expr.kind = Box::new(ExprKind::App {
                    head: Expr {
                        kind: Box::new(ExprKind::GlobalId(
                            crate::names::rust_primitives::hax::explicit_monadic::lift,
                        )),
                        ty: Ty(Box::new(TyKind::Arrow {
                            inputs: vec![inner.ty.clone()],
                            output: inner.ty.clone(),
                        })),
                        meta: Metadata {
                            span: expr.meta.span.clone(),
                            attributes: vec![],
                        },
                    },
                    args: vec![expr.clone()],
                    generic_args: vec![],
                    bounds_impls: vec![],
                    trait_: None,
                });
            }
        }
    }
}

impl VisitorWithContext for ExplicitMonadicVisitor {
    fn context(&self) -> Context {
        // TODO: give a proper context to this phase
        Context::Import
    }
}

impl ExplicitMonadicVisitor {
    fn visit_branches(
        &mut self,
        constraint: Option<MonadicStatus>,
        branches: &mut [&mut Expr],
    ) -> MonadicStatus {
        let branches = branches
            .into_iter()
            .map(|branch| {
                let status = self.visit_expr_unconstrained(branch);
                (status, branch)
            })
            .collect::<Vec<(MonadicStatus, _)>>();
        let statuses: HashSet<_> = branches.iter().map(|(status, _)| *status).collect();
        match statuses.into_iter().collect::<Vec<_>>().as_slice() {
            [homogeneous_status] => *homogeneous_status,
            // This is a match with no arm, thus this has any type
            [] => constraint.unwrap_or_default(),
            _heterogeneous_statuses => {
                let constraint = constraint.unwrap_or_default();
                for (branch_status, branch) in branches {
                    self.coerce(branch, branch_status, constraint);
                }
                constraint
            }
        }
    }

    fn visit_expr_unconstrained(&mut self, expr: &mut Expr) -> MonadicStatus {
        self.visit_expr_with_output(None, expr)
    }
    fn visit_expr_constrained(&mut self, constraint: MonadicStatus, expr: &mut Expr) {
        let expr_status = self.visit_expr_with_output(Some(constraint), expr);
        self.coerce(expr, expr_status, constraint);
    }

    fn visit_expr_with_output(
        &mut self,
        constraint: Option<MonadicStatus>,
        expr: &mut Expr,
    ) -> MonadicStatus {
        match &mut *expr.kind {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.visit_expr_with_output(Some(MonadicStatus::Value), condition);

                let mut branches = [Some(then), else_.as_mut()]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                self.visit_branches(constraint, &mut branches)
            }

            // TODO: constants?
            ExprKind::App { head, args, .. } => {
                self.visit_expr_constrained(MonadicStatus::Value, head);
                for arg in args {
                    self.visit_expr_constrained(MonadicStatus::Value, arg);
                }

                if let ExprKind::GlobalId(head) = &*head.kind
                    && head.is_projector()
                {
                    MonadicStatus::Value
                } else {
                    MonadicStatus::Computation
                }
            }
            ExprKind::Array(exprs) => {
                for arg in exprs {
                    self.visit_expr_constrained(MonadicStatus::Value, arg);
                }
                MonadicStatus::Value
            }
            ExprKind::Literal(_) => MonadicStatus::Value,
            ExprKind::Construct { fields, base, .. } => {
                for expr in fields.iter_mut().map(|(_, e)| e).chain(base.iter_mut()) {
                    self.visit_expr_constrained(MonadicStatus::Value, expr);
                }
                MonadicStatus::Value
            }
            ExprKind::Match { scrutinee, arms } => {
                self.visit_expr_constrained(MonadicStatus::Value, scrutinee);
                let mut arms: Vec<_> = arms.iter_mut().collect();
                for arm in &mut arms {
                    if let Some(Guard {
                        kind: GuardKind::IfLet { rhs, .. },
                        ..
                    }) = &mut arm.guard
                    {
                        self.visit_expr_constrained(MonadicStatus::Value, rhs);
                    }
                }

                let mut branches: Vec<_> = arms.iter_mut().map(|arm| &mut arm.body).collect();
                self.visit_branches(constraint, &mut branches)
            }
            ExprKind::Borrow { inner, .. }
            | ExprKind::AddressOf { inner, .. }
            | ExprKind::Deref(inner) => {
                self.visit_expr_constrained(MonadicStatus::Value, inner);
                MonadicStatus::Value
            }
            ExprKind::Let { lhs, rhs, body } => {
                self.visit_expr_constrained(MonadicStatus::Computation, rhs);
                self.visit_expr_constrained(MonadicStatus::Computation, body);
                MonadicStatus::Computation
            }
            ExprKind::GlobalId(global_id) => MonadicStatus::Value,
            ExprKind::LocalId(local_id) => MonadicStatus::Value,
            ExprKind::Ascription { e, ty } => {
                self.visit_expr_constrained(MonadicStatus::Value, e);
                self.visit(ty);
                MonadicStatus::Value
            }
            ExprKind::Assign { lhs, value } => {
                self.visit_expr_constrained(MonadicStatus::Value, value);
                MonadicStatus::Computation
            }
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                todo!()
            }
            ExprKind::Break { value, label } => todo!(),
            ExprKind::Return { value } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                self.visit_expr_constrained(MonadicStatus::Computation, body);
                MonadicStatus::Computation
            }
            ExprKind::Block { body, .. } => self.visit_expr_unconstrained(body),
            ExprKind::Quote { contents } => todo!(),
            ExprKind::Resugared(resugared_expr_kind) => todo!(),
            ExprKind::Error(error_node) => todo!(),
        }
    }
}

impl AstVisitorMut for ExplicitMonadicVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, x: &mut Expr) {
        self.visit_expr_constrained(MonadicStatus::Computation, x)
    }
}
