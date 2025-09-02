//! A phase rewrites the AST.

use crate::ast::Item;

/// Placeholder trait for phases.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);
}
