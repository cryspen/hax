//! Diagnostic types used to represent and propagate errors (or warnings, notes,
//! etc.) within the AST.
//!
//! This module is used to attach semantic or translation errors to AST nodes.

use crate::ast::*;
use hax_rust_engine_macros::*;

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

/// Description of the error
#[derive_group_for_ast]
pub enum DiagnosticInfoKind {
    /// Custom error
    Custom(String),
    /// Import of a parameter without pattern
    ImportParamWithoutPattern,
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
    pub fn new(node: Fragment, info: DiagnosticInfo) -> Self {
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
