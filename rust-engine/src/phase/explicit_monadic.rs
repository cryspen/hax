//! Monadic Phase
//!
//! This module defines a phase that makes the monadic encoding explicit by introducing calls to hax
//! primitives (`pure` and `lift`) when necessary.
//!
//! # Details
//!
//! In backends with a monadic encoding (Lean for instance), rust computations that can *crash* are
//! wrapped in an error Monad (say `Result`): a function `fn f(x:u32) -> u32` will be extracted to
//! something like `def f (x:u32) : Result u32`. There are two challenges in this encoding :
//!
//! 1. Some expressions cannot panic (literals, consts, constructors for enums, etc) and should be
//!    wrapped in the monad[^coe]. This phase inserts explicit calls to `pure` to that aim.
//!
//! 2. Language constructs (if-then-else, `match`, etc.) and rust functions still expect rust values
//!    as input, not monadic ones. This phase inserts explicit calls to `lift` to materialize the
//!    sub-expressions that return a monadic result where a value is expected. The Lean backend turns
//!    them into explicit lifts `(← ..)`, which implicitly introduces a monadic bind
//!
//! This phase expects all function and closure bodies to be monadic computations by default.
//!
//! [^coe]: While implicit coercions can sometime be enough, they can also badly interact with
//! inference, typically when dealing with branches (like if-then-else) where some branches are
//! pure and some are not.
use std::fmt::Debug;

use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Placeholder struct for the Monadic phase
#[derive(Default, Debug)]
pub struct ExplicitMonadic;

/// Stateless visitor
#[setup_error_handling_struct]
#[derive(Default)]
pub struct ExplicitMonadicVisitor;

/// Status of a rust expression. Computations are possibly panicking, while values are pure
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum MonadicStatus {
    Computation,
    Value,
}

impl Phase for ExplicitMonadic {
    fn apply(&self, items: &mut Vec<Item>) {
        ExplicitMonadicVisitor::default().visit(items)
    }
}

impl ExplicitMonadicVisitor {
    /// Helper to coerce a expression into a given status. `from` should be the status of `expr`
    fn coerce(&mut self, expr: &mut Expr, from: MonadicStatus, to: MonadicStatus) {
        // If the status is already correct, nothing to do.
        if from == to {
            return;
        }
        let inner = expr.clone();
        match to {
            // from = Value, to = Computation : we insert `pure`
            MonadicStatus::Computation => {
                // This is quite verbose because the rust-engine lacks API to build AST nodes
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
            // from = Computation, to = Value : we insert `lift`
            MonadicStatus::Value => {
                // This is quite verbose because the rust-engine lacks API to build AST nodes
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
        Context::Phase(stringify!(ExplicitMonadic).into())
    }
}

impl ExplicitMonadicVisitor {
    fn visit_expr_coerce(&mut self, constraint: MonadicStatus, expr: &mut Expr) {
        // Expression can force a status (returned as `Some(...)`), or be "transparent" (typically
        // for control-flow) and just propagate the constraint.
        let opt_status = match &mut *expr.kind {
            // Control flow nodes
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.visit_expr_coerce(MonadicStatus::Value, condition);
                [Some(then), else_.as_mut()]
                    .into_iter()
                    .flatten()
                    // The constraint is propagated on each branch
                    .for_each(|branch| self.visit_expr_coerce(constraint, branch));
                // No need to coerce the `If` node itself, the coercion is propagated on branches
                None
            }
            ExprKind::Match { scrutinee, arms } => {
                self.visit_expr_coerce(MonadicStatus::Value, scrutinee);
                arms.iter_mut()
                    // The constraint is propagated on each arm
                    .for_each(|arm| {
                        if let Some(Guard {
                            kind: GuardKind::IfLet { rhs, .. },
                            ..
                        }) = &mut arm.guard
                        {
                            self.visit_expr_coerce(MonadicStatus::Value, rhs);
                        };
                        self.visit_expr_coerce(constraint, &mut arm.body)
                    });
                None
            }
            ExprKind::Block { body, .. } => {
                self.visit_expr_coerce(constraint, body);
                None
            }
            ExprKind::Break { .. }
            | ExprKind::Return { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Loop { .. } => {
                unreachable_by_invariant!(Functionalize_loops)
            }
            // Opaque nodes
            ExprKind::Let { lhs: _, rhs, body } => {
                self.visit_expr_coerce(MonadicStatus::Computation, rhs);
                self.visit_expr_coerce(MonadicStatus::Computation, body);
                Some(MonadicStatus::Computation)
            }
            ExprKind::App { head, args, .. } => {
                self.visit_expr_coerce(MonadicStatus::Value, head);
                args.iter_mut()
                    .for_each(|arg| self.visit_expr_coerce(MonadicStatus::Value, arg));
                if let ExprKind::GlobalId(head) = &*head.kind
                    && head.is_projector()
                {
                    // Constructors for structures and enums are values
                    Some(MonadicStatus::Value)
                } else {
                    // Other function calls are computations
                    Some(MonadicStatus::Computation)
                }
            }
            ExprKind::Array(exprs) => {
                exprs
                    .iter_mut()
                    .for_each(|expr| self.visit_expr_coerce(MonadicStatus::Value, expr));
                Some(MonadicStatus::Value)
            }
            ExprKind::Construct { fields, base, .. } => {
                fields
                    .iter_mut()
                    .map(|(_, e)| e)
                    .chain(base.iter_mut())
                    .for_each(|expr| self.visit_expr_coerce(MonadicStatus::Value, expr));
                Some(MonadicStatus::Value)
            }
            ExprKind::Assign { value: inner, .. }
            | ExprKind::Borrow { inner, .. }
            | ExprKind::AddressOf { inner, .. }
            | ExprKind::Deref(inner) => {
                self.visit_expr_coerce(MonadicStatus::Value, inner);
                Some(MonadicStatus::Value)
            }
            ExprKind::Ascription { e, ty } => {
                self.visit_expr_coerce(MonadicStatus::Value, e);
                self.visit(ty);
                Some(MonadicStatus::Value)
            }
            ExprKind::Closure {
                params: _,
                body,
                captures,
            } => {
                captures
                    .iter_mut()
                    .for_each(|capture| self.visit_expr_coerce(MonadicStatus::Value, capture));
                self.visit_expr_coerce(MonadicStatus::Computation, body);
                Some(MonadicStatus::Value)
            }
            ExprKind::Literal(_)
            | ExprKind::GlobalId(_)
            | ExprKind::LocalId(_)
            | ExprKind::Quote { .. }
            | ExprKind::Error(_) => Some(MonadicStatus::Value),
            ExprKind::Resugared(_) => {
                unreachable!("Resugarings should happen after phases")
            }
        };
        if let Some(status) = opt_status {
            self.coerce(expr, status, constraint)
        }
    }
}

impl AstVisitorMut for ExplicitMonadicVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, x: &mut Expr) {
        // Entry points are functions (items and impl items), which start with a `do` block,
        // therefore a monadic computation
        self.visit_expr_coerce(MonadicStatus::Computation, x)
    }

    fn visit_ty(&mut self, x: &mut Ty) {
        if let TyKind::Array { length, .. } = x.kind_mut() {
            self.visit_expr_coerce(MonadicStatus::Value, length);
        };
    }
}
