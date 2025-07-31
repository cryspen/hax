//! Diagnostic types used to represent and propagate errors (or warnings, notes,
//! etc.) within the AST.
//!
//! This module is used to attach semantic or translation errors to AST nodes.

use crate::ast::*;
use hax_rust_engine_macros::*;

pub use hax_types::diagnostics::Kind as DiagnosticInfoKind;

/// Error diagnostic
#[derive_group_for_ast]
pub struct Diagnostic {
    node: Box<Fragment>,
    info: DiagnosticInfo,
}

/// Error description and location
#[derive_group_for_ast]
pub struct DiagnosticInfo {
    /// Diagnostic context
    pub context: Context,
    /// Location in the source code
    pub span: Span,
    /// Error type
    pub kind: DiagnosticInfoKind,
}

impl Diagnostic {
    /// Get diagnostic information
    pub fn info(&self) -> &DiagnosticInfo {
        &self.info
    }
    /// Get diagnostic node of origin
    pub fn node(&self) -> &Fragment {
        &self.node
    }
    /// Report an error
    pub fn new(node: impl Into<Fragment>, info: DiagnosticInfo) -> Self {
        let node = node.into();
        eprintln!("Todo, error reporting");
        eprintln!("node={node:#?}");
        eprintln!("info={info:#?}");
        Self {
            node: Box::new(node),
            info,
        }
    }
}

/// Context of an error
#[derive_group_for_ast]
pub enum Context {
    /// Error during import from THIR
    Import,
}
