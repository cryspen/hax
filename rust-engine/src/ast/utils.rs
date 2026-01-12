//! This module provides a collection of utilities to work on AST.

use super::visitors::*;
use super::*;
use identifiers::*;
use std::collections::HashMap;

/// Useful visitor to map AST fragments.
pub mod mappers {
    use super::*;

    /// Visitor that substitutes local identifiers in ASTs.
    pub struct SubstLocalIds(HashMap<LocalId, LocalId>);

    impl SubstLocalIds {
        /// Create a substituer given one replacement couple.
        pub fn one(from: LocalId, to: LocalId) -> Self {
            Self::many([(from, to)])
        }
        /// Create a substituer given a bunch of replacement couples.
        pub fn many(replacements: impl IntoIterator<Item = (LocalId, LocalId)>) -> Self {
            Self(replacements.into_iter().collect())
        }
    }

    impl AstVisitorMut for SubstLocalIds {
        fn visit_local_id(&mut self, local_id: &mut LocalId) {
            if let Some(replacement) = self.0.get(local_id) {
                *local_id = replacement.clone();
            }
        }
    }
}

impl Metadata {
    /// Get an iterator over hax attributes for this AST fragment.
    pub fn hax_attributes(&self) -> impl Iterator<Item = &hax_lib_macros_types::AttrPayload> {
        crate::attributes::hax_attributes(&self.attributes)
    }
}

impl Pat {
    /// Expects the pattern to be a simple binding `self`.
    pub fn expect_self(&self) -> Option<LocalId> {
        if let PatKind::Binding { var, .. } = self.kind()
            && var.is_self()
        {
            Some(var.clone())
        } else {
            None
        }
    }
}

impl Item {
    /// Returns a `LocalId` named `self` if the item is a standalone function
    /// whose first argument is the keyword `self`. In other words, this
    /// function returns a local identifier only for associated methods from
    /// inherent `impl` blocks.
    pub fn self_id(&self) -> Option<LocalId> {
        if let ItemKind::Fn { params, .. } = self.kind()
            && let [first, ..] = &params[..]
            && let Some(self_id) = first.pat.expect_self()
        {
            Some(self_id.clone())
        } else {
            None
        }
    }
}
