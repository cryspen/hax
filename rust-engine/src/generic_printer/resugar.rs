//! This module defines the resugar fragment for the printer.

use crate::ast::{identifiers::GlobalId, *};
use hax_rust_engine_macros::derive_group_for_ast_base;

/// Extra variants for [`ExprKind`].
/// This is a resugaring view on [`ExprKind`].
#[derive_group_for_ast_base]
pub enum ResugaredExprKind {
    /// A constant with applied generics
    ConstantApp {
        /// The constant
        constant: GlobalId,
        /// The generics
        generics: Vec<GenericValue>,
    },
}

/// Extra variants for [`PatKind`].
/// This is a resugaring view on [`ExprKind`].
#[derive_group_for_ast_base]
pub enum ResugaredPatKind {}

/// Extra variants for [`TyKind`].
/// This is a resugaring view on [`TyKind`].
#[derive_group_for_ast_base]
pub enum ResugaredTyKind {}
