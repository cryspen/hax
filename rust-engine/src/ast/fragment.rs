//! Enumeration types of any possible fragment of AST (`Fragment` / `FragmentRef`).
//!
//! Many components (diagnostics, logging, printers) want to refer to “some AST
//! node” without knowing its concrete type. This module provides:
//! - [`Fragment`]: an **owned** enum covering core AST node types.
//! - [`FragmentRef`]: a **borrowed** counterpart.
//!
//! These are handy when implementing generic facilities such as error reporters,
//! debugging helpers, or pretty-printers that need to branch on “what kind of
//! node is this?” at runtime.
//!
//! ## Notes
//! - Both enums are mechanically generated to stay in sync with the canonical
//!   AST types. If you add a new core AST node, update the macro invocation at
//!   the bottom of this file so `Fragment`/`FragmentRef` learn about it.
//! - The [`Unknown`] variant exists as a last-resort placeholder when a value
//!   cannot be represented by a known variant. Prefer concrete variants when
//!   possible.

use crate::ast::*;

/// The `mk!` macro takes a flat list of AST type identifiers and expands to
/// two enums:
/// - `Fragment` with owned variants (`Foo(Foo)`), and
/// - `FragmentRef<'a>` with borrowed variants (`Foo(&'a Foo)`).
///
/// The generated enums also implement the obvious `From<T>` conversions, making
/// it ergonomic to wrap concrete AST values as fragments.
macro_rules! mk {
    ($($ty:ident),*) => {
        #[derive_group_for_ast]
        #[allow(missing_docs)]
        /// An owned fragment of AST in hax.
        pub enum Fragment {
            $(
                #[doc = concat!("An owned [`", stringify!($ty), "`] node.")]
                $ty($ty),
            )*
            /// Represent an unknown node in the AST with a message.
            Unknown(String),
        }
        #[derive(Copy)]
        #[derive_group_for_ast_base]
        #[derive(::serde::Serialize)]
        #[allow(missing_docs)]
        /// A borrowed fragment of AST in hax.
        pub enum FragmentRef<'lt> {
            $(
                #[doc = concat!("A borrowed [`", stringify!($ty), "`] node.")]
                $ty(&'lt $ty),
            )*
        }

        $(
            impl From<$ty> for Fragment {
                fn from(fragment: $ty) -> Self {
                    Self::$ty(fragment)
                }
            }
            impl<'lt> From<&'lt $ty> for FragmentRef<'lt> {
                fn from(fragment: &'lt $ty) -> Self {
                    Self::$ty(fragment)
                }
            }
        )*
    };
}

#[hax_rust_engine_macros::replace(AstNodes => include(VisitableAstNodes))]
mk!(GlobalId, AstNodes);
