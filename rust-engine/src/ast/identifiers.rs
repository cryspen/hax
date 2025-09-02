//! Identifier types used throughout the AST.
//!
//! This module defines:
//! - `GlobalId`: fully-qualified paths like `std::mem::drop`
//! - `LocalId`: local variable identifiers

use crate::symbol::Symbol;
use hax_rust_engine_macros::*;
use std::fmt;

pub mod global_id;
/// Local identifier
#[derive_group_for_ast]
pub struct LocalId(pub Symbol);

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl From<&hax_frontend_exporter::LocalIdent> for LocalId {
    fn from(value: &hax_frontend_exporter::LocalIdent) -> Self {
        Self(Symbol::new(&value.name))
    }
}
impl From<&str> for LocalId {
    fn from(name: &str) -> Self {
        Self(Symbol::new(name))
    }
}

pub use global_id::GlobalId;
