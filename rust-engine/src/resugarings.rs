//! The "resugaring" phases used by printers.

//! This module defines resugarings instances (see
//! [`hax_rust_engine::ast::Resugaring`] for the definition of a
//! resugaring). Each backend defines its own set of resugaring phases.

use crate::ast::identifiers::global_id::ExplicitDefId;
use crate::ast::resugared::*;
use crate::ast::visitors::*;
use crate::ast::*;
use crate::printer::*;
use std::collections::HashSet;

/// Transforms [`ItemKind::Fn`] of arity zero into [`ResugaredItemKind::Constant`].
/// Rust `const` items are encoded by the `ImportThir` phase of the hax engine as function of arity zero.
/// Functions of arity zero themselves are encoded as functions operating on one argument of type `()`.
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
        if !params.is_empty() {
            return;
        }
        *item_kind = ItemKind::Resugared(ResugaredItemKind::Constant {
            name: name.clone(),
            body: body.clone(),
            generics: generics.clone(),
        });
    }
}

impl Resugaring for FunctionsToConstants {
    fn name(&self) -> String {
        "functions-to-constants".to_string()
    }
}

/// Binop resugaring. Used to identify expressions of the form `(f e1 e2)` where
/// `f` is a known identifier.
pub struct BinOp {
    /// Stores a set of identifiers that should be resugared as binary
    /// operations. Usually, those identifiers come from the hax encoding. Each
    /// backend can select its own set of identifiers Typically, if the backend
    /// has a special support for addition, `known_ops` will contain
    /// `hax::machine::int::add`
    pub known_ops: HashSet<ExplicitDefId>,
}

impl BinOp {
    /// Adds a new binary operation from a list of (hax-introduced) names
    pub fn new(known_ops: &[ExplicitDefId]) -> Self {
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
