//! The Rust engine of hax.

#![feature(rustc_private)]
#![warn(
    rustdoc::broken_intra_doc_links,
    missing_docs,
    unused_qualifications,
    unused_crate_dependencies
)]

pub mod ast;
pub mod backends;
pub mod hax_io;
pub mod names;
pub mod ocaml_engine;
pub mod phase;
pub mod printer;
pub mod resugarings;
pub mod symbol;
