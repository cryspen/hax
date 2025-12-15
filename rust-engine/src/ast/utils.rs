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
