//! Interned string identifiers used throughout the AST.
//!
//! Symbols are lightweight wrappers around `String` for use in identifiers.
//! Eventually, this could be backed by a real interner or arena.

use std::ops::Deref;

use hax_rust_engine_macros::*;

/// Interned string identifier for the AST
#[derive_group_for_ast]
pub struct Symbol(String);

impl Symbol {
    /// Create a new symbol
    pub fn new(s: impl AsRef<str>) -> Self {
        Self(s.as_ref().to_string())
    }
}

impl Deref for Symbol {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}
