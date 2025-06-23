//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use crate::printer::Allocator;
use pretty::{docs, DocAllocator, DocBuilder, Pretty};

use crate::ast::{Item, ItemKind};

macro_rules! todo {
    ($allocator:ident) => {
        $allocator.text("Todo")
    };
}

/// Placeholder structure for lean printer
pub struct Lean;

impl<'a, A: 'a> Pretty<'a, Allocator<Lean>, A> for Item {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!(allocator)
    }
}

impl<'a, A: 'a> Pretty<'a, Allocator<Lean>, A> for ItemKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!(allocator)
    }
}
