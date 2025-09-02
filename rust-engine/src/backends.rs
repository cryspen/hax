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

pub mod lean;
pub mod rust;

use std::collections::HashMap;

use crate::{
    ast::{Item, Metadata, Module, span::Span},
    printer::{Print, Printer},
};
use camino::Utf8PathBuf;
use hax_types::engine_api::File;

/// A hax backend.
///
/// A backend is responsible for turning the hax AST into sources of a target language.
/// It combines:
/// - a sequence of AST transformation phases, and
/// - a printer that generates textual output.
///
/// For example, we have F\*, Coq, and Lean backends.
/// Some are still in the old OCaml engine.
pub trait Backend {
    /// The printer type used by this backend.
    type Printer: Printer;

    /// Construct a new printer instance.
    ///
    /// By default this calls `Default::default` on the printer type.
    fn printer(&self) -> Self::Printer {
        Self::Printer::default()
    }

    /// A short name identifying the backend.
    ///
    /// By default, this is delegated to the associated printer's [`Printer::NAME`].
    const NAME: &'static str = Self::Printer::NAME;

    /// The AST phases to apply before printing.
    ///
    /// Backends can override this to add transformations.
    /// The default is an empty list (no transformations).
    fn phases(&self) -> Vec<Box<dyn crate::phase::Phase>> {
        vec![]
    }

    /// Group a flat list of items into modules.
    fn items_to_module(&self, items: Vec<Item>) -> Vec<Module> {
        let mut modules: HashMap<_, Vec<_>> = HashMap::new();
        for item in items {
            let concrete_ident = item.ident.as_concrete().unwrap();
            let module_ident = concrete_ident.mod_only_closest_parent();

            modules.entry(module_ident).or_default().push(item);
        }
        modules
            .into_iter()
            .map(|(ident, items)| Module {
                ident: ident.clone().into_concrete(),
                items,
                meta: Metadata {
                    span: Span::dummy(),
                    attributes: vec![],
                },
            })
            .collect()
    }

    /// Compute the relative filesystem path where a given module should be written.
    fn module_path(&self, module: &Module) -> Utf8PathBuf;
}

/// Apply a backend to a collection of AST items, producing output files.
///
/// This runs all of the backend's [`Backend::phases`], groups the items into
/// modules via [`Backend::items_to_module`], and then uses the backend's printer
/// to generate source files with paths determined by [`Backend::module_path`].
pub fn apply_backend<B: Backend + 'static>(backend: B, mut items: Vec<Item>) -> Vec<File> {
    for phase in backend.phases() {
        phase.apply(&mut items);
    }

    let modules = backend.items_to_module(items);
    modules
        .into_iter()
        .map(|module: Module| {
            let path = backend.module_path(&module).into_string();
            let (contents, _) = backend.printer().print(module);
            File {
                path,
                contents,
                sourcemap: None,
            }
        })
        .collect()
}

#[allow(unused)]
mod prelude {
    //! Small "bring-into-scope" set used by backend modules.
    //!
    //! Importing this prelude saves repetitive `use` lists in per-backend
    //! modules without forcing these names on downstream users.
    pub use super::Backend;
    pub use crate::ast::identifiers::global_id::view::AnyKind;
    pub use crate::ast::identifiers::*;
    pub use crate::ast::literals::*;
    pub use crate::ast::resugared::*;
    pub use crate::ast::*;
    pub use crate::printer::render_view::*;
    pub use crate::printer::*;
    pub use crate::symbol::Symbol;
    pub use hax_rust_engine_macros::prepend_associated_functions_with;
    pub use pretty::DocAllocator;
    pub use pretty::DocBuilder;
    pub use pretty::Pretty;
    pub use pretty_ast::install_pretty_helpers;
}
