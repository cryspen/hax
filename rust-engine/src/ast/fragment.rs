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
    (@visit_inner_call, Span, $self:ident, $x:expr) => {::std::ops::ControlFlow::Continue(())};
    (@visit_inner_call, GloablId, $self:ident, $x:expr) => {::std::ops::ControlFlow::Continue(())};
    (@visit_inner_call, $ty:ty, $self:ident, $x:expr) => {
        $self.visit_inner($x)
    };
    ($($ty:ident),*) => {
        #[derive_group_for_ast]
        #[derive(Copy)]
        /// Type identifiers for fragments
        pub enum FragmentTypeId {
            $(
                #[doc = concat!("An identifier for the type [`", stringify!($ty), "`].")]
                $ty,
            )*
        }

        mod private {
            pub use super::*;
            pub trait Sealed {}
            $(impl Sealed for $ty {})*
        }

        /// Operations on any fragment of the AST of hax.
        pub trait AnyFragment: private::Sealed {
            /// Get a type identifier for this fragment.
            fn type_id() -> FragmentTypeId;
            /// Coerce as a fragment reference.
            fn as_fragment<'a>(&'a self, type_id: FragmentTypeId) -> Option<FragmentRef<'a>>;
            /// Coerce as an owned fragment.
            fn as_owned_fragment(&self, type_id: FragmentTypeId) -> Option<Fragment>;
        }

        $(
            impl AnyFragment for $ty {
                fn type_id() -> FragmentTypeId {
                    FragmentTypeId::$ty
                }
                fn as_fragment<'a>(&'a self, type_id: FragmentTypeId) -> Option<FragmentRef<'a>> {
                    if type_id == Self::type_id() {
                        Some(self.into())
                    } else {
                        None
                    }
                }
                fn as_owned_fragment(&self, type_id: FragmentTypeId) -> Option<Fragment> {
                    if type_id == Self::type_id() {
                        #[allow(unreachable_code)]
                        Some(self.clone().into())
                    } else {
                        None
                    }
                }
            }
        )*

        /// A marker about a sub AST fragment in a bigger AST.
        pub struct FragmentMarker {
            addr: usize,
            type_id: fragment::FragmentTypeId,
        }

        impl FragmentMarker {
            /// Creates a marker out of an AST fragment.
            pub fn new<T: AnyFragment>(value: &T) -> Self {
                Self {
                    addr: (value as *const T).addr(),
                    type_id: T::type_id(),
                }
            }
        }


        impl<'a> derive_generic_visitor::Visitor for FragmentMarker {
            type Break = Fragment;
        }

        impl visitors::AstEarlyExitVisitor for FragmentMarker {
            $(
                pastey::paste!{
                    fn [<visit_ $ty:snake>](&mut self, x: &$ty) -> ::std::ops::ControlFlow<Self::Break> {
                        if self.addr == (x as *const $ty).addr()
                            && let Some(fragment) = x.as_owned_fragment(self.type_id)
                        {
                            return ::std::ops::ControlFlow::Break(fragment);
                        }
                        mk!(@visit_inner_call, $ty, self, x)
                    }
                }
            )*
        }

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
mk!(GlobalId, Span, AstNodes);
