//! This module defines *resugared fragments* for the Hax Rust engine's AST.
//!
//! A resugared fragment is an additional AST node used solely for pretty-printing purposes.
//! These nodes carry no semantic meaning in hax core logic but enable more accurate
//! or backend-specific surface syntax reconstruction.
//!
//! For example, the engine represents the `unit` type as a zero-sized tuple `()`,
//! mirroring Rust's internal representation. However, this may not suit all backends:
//! in F*, `unit` is explicitly written as `unit`, not `()`.
//!
//! To accommodate such differences, we introduce resugared fragments (e.g. `UnitType`) that
//! allow the printer to emit the expected syntax while maintaining the same internal semantics.

use hax_rust_engine_macros::*;

/// Resugared variants for items. This represent extra printing-only items, see [`super::ItemKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredItemKind {}

/// Resugared variants for expressions. This represent extra printing-only expressions, see [`super::ExprKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredExprKind {}

/// Resugared variants for patterns. This represent extra printing-only patterns, see [`super::PatKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredPatKind {}

/// Resugared variants for types. This represent extra printing-only types, see [`super::TyKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredTyKind {}

/// Resugared variants for impl. items. This represent extra printing-only impl. items, see [`super::ImplItemKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredImplItemKind {}

/// Resugared variants for trait items. This represent extra printing-only trait items, see [`super::TraitItemKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredTraitItemKind {}

/// Marks a type as a resugar fragment of the AST.
pub trait ResugaredFragment {
    /// What fragment of the AST this resugar is extending?
    type ParentFragment;
}

/// Convenience macro which implements [`ResugaredFragment`] on `$ty`, setting
/// `$parent` as the `ParentFragment`, as well as `From<$ty>` for `$parent`, by
/// wrapping the `$ty` in `$parent::Resugared(..)`.
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
