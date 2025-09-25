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

use super::*;

/// Resugared variants for items. This represent extra printing-only items, see [`super::ItemKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredItemKind {
    /// A `const` item, for example `const NAME: T = body;`.
    /// The type of the constant is `body.ty`.
    Constant {
        /// The identifier of the constant, for example `krate::module::NAME`.
        name: GlobalId,
        /// The body of the constant, for example `body`.
        body: Expr,
        /// The generic arguments and constraints of the constant.
        /// Note: constant supporting generics is a nightly feature (generic_const_items).
        generics: Generics,
    },
}

/// Resugared variants for expressions. This represent extra printing-only expressions, see [`super::ExprKind::Resugared`].
#[derive_group_for_ast]
// TODO: drop `clippy::large_enum_variant` when https://github.com/cryspen/hax/issues/1666 is addressed.
#[allow(clippy::large_enum_variant)]
pub enum ResugaredExprKind {
    /// Binary operations (identified by resugaring) of the form `f(e1, e2)`
    BinOp {
        /// The identifier of the operation (`f`)
        op: GlobalId,
        /// The left-hand side of the operation (`e1`)
        lhs: Expr,
        /// The right-hand side of the operation (`e2`)
        rhs: Expr,
        /// The generic arguments applied to the function.
        generic_args: Vec<GenericValue>,
        /// If the function requires generic bounds to be called, `bounds_impls`
        /// is a vector of impl. expressions for those bounds.
        bounds_impls: Vec<ImplExpr>,
        /// If we apply an associated function, contains the impl. expr used.
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
    },
    /// A tuple constructor.
    ///
    /// # Example:
    /// `(a, b)`
    Tuple(Vec<Expr>),
}

/// Resugared variants for patterns. This represent extra printing-only patterns, see [`super::PatKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredPatKind {}

/// Resugared variants for types. This represent extra printing-only types, see [`super::TyKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredTyKind {
    /// A tuple tupe.
    ///
    /// # Example:
    /// `(i32, bool)`
    Tuple(Vec<Ty>),
}

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
    ResugaredItemKind => ItemKind,
    ResugaredExprKind => ExprKind,
    ResugaredPatKind => PatKind,
    ResugaredTyKind => TyKind,
    ResugaredImplItemKind => ImplItemKind,
    ResugaredTraitItemKind => TraitItemKind
);
