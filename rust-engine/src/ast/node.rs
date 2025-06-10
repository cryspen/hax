//! The `Node` type for holding arbitrary AST fragments.
//!
//! This enum is useful for diagnostics or dynamic dispatch on generic AST values.
//! It acts as a type-erased wrapper around various core AST node types.

use crate::ast::*;

include!("generated/node.rs");
