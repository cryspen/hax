//! This module defines the resugar fragment for the printer.

use crate::ast::*;

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredExprKind {
    ConstantApp {
        constant: GlobalId,
        generics: GenericValue,
    },
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredPatKind {}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ResugaredTy {}
