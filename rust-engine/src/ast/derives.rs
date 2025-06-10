//! This module defines a few aliases for groups of derive clauses that are
//! common and repeated a lot thoughtout the AST and its helper types.
//!
//! Instead of writting the same `#[derive(...)]` clause on top of each item of
//! the AST, we just write `#[apply(derive_AST)]`, given `apply` and
//! `derive_AST` are in scope.

pub use macro_rules_attribute::{apply, attribute_alias};

attribute_alias! {
    #[apply(derive_AST)] = #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)];
    #[apply(derive_AST_base)] = #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)];
}
