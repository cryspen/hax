//! The Rust engine of hax.

#![feature(rustc_private)]
#![feature(fn_traits, unboxed_closures)]
#![warn(
    rustdoc::broken_intra_doc_links,
    missing_docs,
    unused_qualifications,
    unused_crate_dependencies
)]

pub mod ast;
pub mod backends;
pub mod debugger;
pub mod hax_io;
pub mod import_thir;
pub mod interning;
pub mod names;
pub mod ocaml_engine;
pub mod phase;
pub mod printer;
pub mod resugarings;
pub mod symbol;
