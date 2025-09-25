//! A phase rewrites the AST.

/// Placeholder trait for phases.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);
}

use std::collections::HashSet;

use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};

#[derive(Default)]
pub struct ExplicitMonadic;

#[setup_error_handling_struct]
#[derive(Default)]
pub struct ExplicitMonadicVisitor {
    required: MonadicStatus,
    output: MonadicStatus,
}

#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
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
    fn coerce(&self, expr: &mut Expr, expr_status: MonadicStatus) {
        if expr_status == self.required {
            return;
        }
        let inner = expr.clone();
        match self.required {
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

    fn with_requirement<V>(
        &mut self,
        value: &mut V,
        req: MonadicStatus,
        f: impl Fn(&mut Self, &mut V) -> (),
    ) -> MonadicStatus {
        let req_init = self.required;
        self.required = req;
        f(self, value);
        self.required = req_init;
        self.output
    }

    fn visit_expr_with_requirement(
        &mut self,
        expr: &mut Expr,
        req: MonadicStatus,
    ) -> MonadicStatus {
        self.with_requirement(expr, req, |this, expr| this.visit_expr(expr))
    }
}

impl VisitorWithContext for ExplicitMonadicVisitor {
    fn context(&self) -> Context {
        // TODO: give a proper context to this phase
        Context::Import
    }
}

impl AstVisitorMut for ExplicitMonadicVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        self.output = match &mut *expr.kind {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.visit_expr_with_requirement(condition, MonadicStatus::Value);
                self.visit_expr(then);
                let then_status = self.output;
                let else_status = else_
                    .as_mut()
                    .map(|else_| {
                        self.visit_expr(else_);
                        self.output
                    })
                    .unwrap_or(then_status);

                if else_status == then_status {
                    else_status
                } else {
                    self.coerce(then, then_status);
                    if let Some(else_) = else_ {
                        self.coerce(else_, then_status);
                    }
                    self.required
                }
            }

            // TODO: constants?
            ExprKind::App { head, args, .. } => {
                self.visit_expr_with_requirement(head, MonadicStatus::Value);
                for arg in args {
                    self.visit_expr_with_requirement(arg, MonadicStatus::Value);
                }
                MonadicStatus::Computation
            }
            ExprKind::Array(exprs) => {
                for arg in exprs {
                    self.visit_expr_with_requirement(arg, MonadicStatus::Value);
                }
                MonadicStatus::Value
            }
            ExprKind::Literal(_) => MonadicStatus::Value,
            ExprKind::Construct { fields, base, .. } => {
                for (_, expr) in fields {
                    self.coerce(expr, MonadicStatus::Value);
                }
                self.coerce(base, MonadicStatus::Value);

                MonadicStatus::Value
            }
            ExprKind::Match { scrutinee, arms } => {
                self.visit_expr_with_requirement(scrutinee, MonadicStatus::Value);
                for arm in arms {
                    if let Some(Guard {
                        kind: GuardKind::IfLet { rhs, .. },
                        ..
                    }) = &mut arm.guard
                    {
                        self.visit_expr_with_requirement(rhs, MonadicStatus::Value);
                    }
                }
                let statuses = arms
                    .iter_mut()
                    .map(|arm| {
                        self.visit_arm(arm);
                        self.output
                    })
                    .collect::<HashSet<MonadicStatus>>();
                match statuses.iter().collect().as_slice() {
                    [homogeneous_status] => homogeneous_status,
                    [] => self.required,
                    _heterogeneous_statuses => {
                        for arm in arms {
                            self.visit_expr_with_requirement(&mut arm.body, self.required);
                        }
                        self.required
                    }
                }
            }
            ExprKind::Borrow { mutable, inner } => todo!(),
            ExprKind::AddressOf { mutable, inner } => todo!(),
            ExprKind::Deref(expr) => todo!(),
            ExprKind::Let { lhs, rhs, body } => todo!(),
            ExprKind::GlobalId(global_id) => todo!(),
            ExprKind::LocalId(local_id) => todo!(),
            ExprKind::Ascription { e, ty } => todo!(),
            ExprKind::Assign { lhs, value } => todo!(),
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => todo!(),
            ExprKind::Break { value, label } => todo!(),
            ExprKind::Return { value } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => todo!(),
            ExprKind::Block { body, safety_mode } => todo!(),
            ExprKind::Quote { contents } => todo!(),
            ExprKind::Resugared(resugared_expr_kind) => todo!(),
            ExprKind::Error(error_node) => todo!(),
        };
        self.coerce(expr, self.output);
    }
}
