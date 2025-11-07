//! This module contains type definitions that have no equivalent in
//! Rustc.

#[cfg(feature = "rustc")]
mod builtin_types;
mod full_def;
mod impl_infos;
mod item_attributes;
mod predicate_id;
mod variant_infos;

#[cfg(feature = "rustc")]
pub use builtin_types::*;
pub use full_def::*;
pub use impl_infos::*;
pub use item_attributes::*;
pub use predicate_id::*;
pub use variant_infos::*;
