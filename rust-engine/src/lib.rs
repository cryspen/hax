//! The Rust engine of hax.

#![feature(rustc_private)]
#![warn(
    rustdoc::broken_intra_doc_links,
    missing_docs,
    unused_qualifications,
    unused_crate_dependencies
)]

pub mod ast;
pub mod symbol;
