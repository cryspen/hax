//! This module provides a view of the AST suited for pretty printing.
//!
//! This view is shallow: the print view datatypes mirror each type of the AST,
//! but every field of each enum variant and each struct variant are wrapped
//! with the type `PrintContext`.

pub mod origin {
    pub use crate::ast::*;
    pub use {bool, Box, Option, String, Vec};

    pub use super::super::resugar::*;
    pub use diagnostics::Diagnostic;
    pub use hax_frontend_exporter::{Impl, Mutability};
    pub use node::Node;
    pub use span::Span;
}
use super::print_context::PrintContext;
use crate::ast::derives::{apply, derive_AST_base as derive_AST};

include!("generated/print_view.rs");
