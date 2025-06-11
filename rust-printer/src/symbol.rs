//! Interned string identifiers used throughout the AST.
//!
//! Symbols are lightweight wrappers around `String` for use in identifiers.
//! Eventually, this could be backed by a real interner or arena.

use hax_rust_engine_macros::*;

#[derive_group_for_ast]
pub struct Symbol(String);

impl Symbol {
    pub fn new(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}
