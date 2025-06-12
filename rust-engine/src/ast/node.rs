//! The `Node` type for holding arbitrary AST fragments.
//!
//! This enum is useful for diagnostics or dynamic dispatch on generic AST values.
//! It acts as a type-erased wrapper around various core AST node types.

use std::ops::Deref;

use crate::ast::*;

include!("generated/node.rs");

impl<'a> From<&'a Box<PatKind>> for NodeRef<'a>
where
    NodeRef<'a>: From<&'a PatKind>,
{
    fn from(value: &'a Box<PatKind>) -> Self {
        value.deref().into()
    }
}
