//! Code generation backends.
//!
//! A backend is consititued of:
//!  - a list of AST transformations to apply, those are called phases.
//!  - and a printer.
//!
//! This top-level module is mostly an index of available backends and a
//! small prelude to make backend modules concise.
//!
//! # Adding a new backend
//! 1. Create a submodule under `src/backends/`, e.g. `foo.rs`.
//! 2. Put your printer and backend there.
//! 3. Re-export it here with `pub mod foo;`.
//!
//! See [`rust`] for an example implementation.

pub mod rust;

#[allow(unused)]
mod prelude {
    //! Small "bring-into-scope" set used by backend modules.
    //!
    //! Importing this prelude saves repetitive `use` lists in per-backend
    //! modules without forcing these names on downstream users.
    pub use crate::ast::*;
    pub use crate::printer::*;
    pub use hax_rust_engine_macros::prepend_associated_functions_with;
    pub use pretty::DocAllocator;
    pub use pretty::Pretty;
    pub use pretty_ast::install_pretty_helpers;
}
