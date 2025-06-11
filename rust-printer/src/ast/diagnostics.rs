//! Diagnostic types used to represent and propagate errors (or warnings, notes,
//! etc.) within the AST.
//!
//! This module is used to attach semantic or translation errors to AST nodes.

use hax_rust_engine_macros::*;
use crate::ast::*;

#[derive_group_for_ast]
pub struct Diagnostic {
    node: Box<Node>,
    info: DiagnosticInfo,
}

#[derive_group_for_ast]
pub struct DiagnosticInfo {
    pub context: Context,
    pub span: Span,
    pub kind: DiagnosticInfoKind,
}

#[derive_group_for_ast]
pub enum DiagnosticInfoKind {
    Custom(String),
    ImportParamWithoutPattern,
}

impl Diagnostic {
    pub fn info(&self) -> &DiagnosticInfo {
        &self.info
    }
    pub fn node(&self) -> &Node {
        &self.node
    }
    pub fn new(node: Node, info: DiagnosticInfo) -> Self {
        eprintln!("Todo, error reporting");
        eprintln!("node={node:#?}");
        eprintln!("info={info:#?}");
        Self {
            node: Box::new(node),
            info,
        }
    }
}

#[derive_group_for_ast]
pub enum Context {
    Import,
}
