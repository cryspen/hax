//! Diagnostic types used to represent and propagate errors (or warnings, notes,
//! etc.) within the AST.
//!
//! This module is used to attach semantic or translation errors to AST nodes.

use crate::ast::*;

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Diagnostic {
    node: Box<Node>,
    info: DiagnosticInfo,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct DiagnosticInfo {
    pub context: Context,
    pub span: Span,
    pub kind: DiagnosticInfoKind,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Context {
    Import,
}
