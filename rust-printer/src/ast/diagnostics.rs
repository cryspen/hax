//! Diagnostic types used to represent and propagate errors (or warnings, notes,
//! etc.) within the AST.
//!
//! This module is used to attach semantic or translation errors to AST nodes.

use crate::ast::derives::*;
use crate::ast::*;

#[apply(derive_AST)]
pub struct Diagnostic {
    node: Box<Node>,
    info: DiagnosticInfo,
}

#[apply(derive_AST)]
pub struct DiagnosticInfo {
    pub context: Context,
    pub span: Span,
    pub kind: DiagnosticInfoKind,
}

#[apply(derive_AST)]
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

#[apply(derive_AST)]
pub enum Context {
    Import,
}
