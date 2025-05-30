//! The `Node` type for holding arbitrary AST fragments.
//!
//! This enum is useful for diagnostics or dynamic dispatch on generic AST values.
//! It acts as a type-erased wrapper around various core AST node types.

use crate::ast::*;

/// An enumeration for representing any kind of AST node. This is useful for diagnostics.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Node {
    GenericValue(GenericValue),
    PrimitiveTy(PrimitiveTy),
    Ty(Ty),
    Metadata(Metadata),
    Expr(Expr),
    Pat(Pat),

    /// A fallback node for unknown or unsupported AST fragments, e.g., we don't represent frontend's AST fragments.
    Unknown(String),
    // TODO: complete
}
