//! This module contains resugared fragments of the AST of hax.
//!
//! In hax, a resugared fragment of AST is an extra node that is relevant only for printers.
//!
//! As an example, we represent (just as Rust does) the type `unit` as a tuple of size zero.
//! This may be unsuited for some backend: in F* for instance, `unit` is not denoted `()` but `unit.`
//! Thus, we add a resugared fragment for the type unit.

use hax_rust_engine_macros::*;

/// Resugared variants for items. This represent extra printing-only items, see [`super::ItemKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredItemKind {}

/// Resugared variants for expressions. This represent extra printing-only expressions, see [`super::ExprKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredExprKind {}

/// Resugared variants for patterns. This represent extra printing-only patterns, see [`super::PatKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredPatKind {}

/// Resugared variants for types. This represent extra printing-only types, see [`super::TyKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredTyKind {
    /// The `unit` type.
    ///
    /// Without resugaring: a tuple of arity zero.
    Unit,
}

/// Resugared variants for impl. items. This represent extra printing-only impl. items, see [`super::ImplItemKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredImplItemKind {}

/// Resugared variants for trait items. This represent extra printing-only trait items, see [`super::TraitItemKind::Resugared`].
#[derive_group_for_ast]
#[visitable]
pub enum ResugaredTraitItemKind {}

/// Marks a type as a resugar fragment of the AST.
pub trait ResugaredFragment {
    /// What fragment of the AST this resugar is extending?
    type ParentFragment;
}

macro_rules! derive_from {
    ($($ty:ty => $parent:ty),*) => {
        $(impl ResugaredFragment for $ty {
            type ParentFragment = $parent;
        }
        impl From<$ty> for <$ty as ResugaredFragment>::ParentFragment {
            fn from(value: $ty) -> Self {
                Self::Resugared(value)
            }
        })*
    };
}

derive_from!(
    ResugaredItemKind => super::ItemKind,
    ResugaredExprKind => super::ExprKind,
    ResugaredPatKind => super::PatKind,
    ResugaredTyKind => super::TyKind,
    ResugaredImplItemKind => super::ImplItemKind,
    ResugaredTraitItemKind => super::TraitItemKind
);
