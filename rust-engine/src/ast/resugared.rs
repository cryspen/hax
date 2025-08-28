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

use crate::resugarings;

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
    },
}

/// Resugared variants for expressions. This represent extra printing-only expressions, see [`super::ExprKind::Resugared`].
#[derive_group_for_ast]
pub enum ResugaredExprKind {
    /// A function application, with special cases for symbols recognized by the engine.
    /// For instance, we know that `core::ops::Add::add` is a binary operator.
    FunApp {
        /// The generic arguments applied to the function.
        generic_args: Vec<GenericValue>,
        /// If the function requires generic bounds to be called, `bounds_impls`
        /// is a vector of impl. expressions for those bounds.
        bounds_impls: Vec<ImplExpr>,
        /// If we apply an associated function, contains the impl. expr used.
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
        /// What know application is this?
        app: FunApp,
        /// The function being applied: the original expression, including its metadata.
        head: Expr,
    },
    /// A tuple constructor.
    ///
    /// # Example:
    /// `(a, b)`
    Tuple(Vec<Expr>),
}

mod fun_app {
    use super::*;
    use crate::ast::identifiers::global_id::{ConcreteId, ExplicitDefId};

    #[derive_group_for_ast]
    /// A function application, with special cases for sumbols recognized by the engine.
    /// Symbols recognized by the engine comes with static guarantees about their arity.
    /// This enum encodes a map between list of known names and static aritites.
    pub enum FunApp {
        /// A nullary application
        Nullary(NullaryName),
        /// An unary application
        Unary(UnaryName, [Expr; 1]),
        /// A binary application
        Binary(BinaryName, [Expr; 2]),
        /// Fallback case for unknown applications
        Unknown {
            /// The argument of the application.
            /// Here there is no head, since the head of the application is already available on [`ResugaredExprKind::App`].
            args: Vec<Expr>,
        },
    }

    impl FunApp {
        /// Tries to destruct a function application to produce a `FunApp`.
        pub fn destruct_function_application(head: &Expr, args: &[Expr]) -> Self {
            (|| {
                let ExprKind::GlobalId(head) = &*head.kind else {
                    return None;
                };
                Some(match args {
                    [] => Self::Nullary(NullaryName::from_global_id(head.clone())?),
                    [a] => Self::Unary(UnaryName::from_global_id(head.clone())?, [a.clone()]),
                    [a, b] => Self::Binary(
                        BinaryName::from_global_id(head.clone())?,
                        [a.clone(), b.clone()],
                    ),
                    _ => return None,
                })
            })()
            .unwrap_or_else(|| Self::Unknown {
                args: args.to_vec(),
            })
        }

        /// Reconstruct a list of argument from a `FunApp`.
        pub fn args(&self) -> &[Expr] {
            match self {
                Self::Nullary(_) => &[],
                Self::Unary(_, args) => &args[..],
                Self::Binary(_, args) => &args[..],
                Self::Unknown { args } => args,
            }
        }
    }

    macro_rules! mk_enum {
        ($(
            $(#$attr:tt)*
            pub enum $enum_name:ident {
                $($variant:ident = $name:expr),*
                $(,)?
            }
        )*) => {$(
            $(#$attr)*
            pub enum $enum_name {
                $(
                    #[doc = concat!("The name `", stringify!($name), "`.")]
                    $variant,
                )*
            }

            impl From<$enum_name> for ExplicitDefId {
                fn from(v: $enum_name) -> ExplicitDefId {
                    match v {
                        $($enum_name::$variant => $name,)*
                    }
                }
            }
            impl From<$enum_name> for ConcreteId {
                fn from(v: $enum_name) -> ConcreteId {
                    ConcreteId {
                        def_id: v.into(),
                        moved: None,
                        suffix: None,
                    }
                }
            }
            impl From<$enum_name> for GlobalId {
                fn from(v: $enum_name) -> GlobalId {
                    GlobalId::Concrete(v.into())
                }
            }

            impl $enum_name {
                #[doc = concat!("Tries to match a global identifier as a [`", stringify!($enum_name), "`]. If the global identifier cannot be turned into a [`", stringify!($enum_name), "`], this method returns `None`.")]
                #[allow(unused_variables)] // in case of empty enums
                pub fn from_global_id(global_id: GlobalId) -> Option<$enum_name> {
                    $(
                        if global_id == $name {
                            return Some($enum_name::$variant);
                        }
                    )*
                    return None;
                }
            }
        )*};
    }

    mod binops {
        pub use crate::names::rust_primitives::hax::machine_int::{
            add, div, mul, rem, shl, shr, sub,
        };
        pub use crate::names::rust_primitives::hax::{logical_op_and, logical_op_or};
    }

    mk_enum! {
        #[derive_group_for_ast]
        /// The names corresponding to callable items of arity 0
        pub enum NullaryName {}

        #[derive_group_for_ast]
        /// The names corresponding to callable items of arity 1
        pub enum UnaryName {
            DerefOp = crate::names::rust_primitives::hax::deref_op(),
            CastOp = crate::names::rust_primitives::hax::cast_op(),
        }

        #[derive_group_for_ast]
        /// The names corresponding to callable items of arity 2
        pub enum BinaryName {
            Add = binops::add(),
            Sub = binops::sub(),
            Mul = binops::mul(),
            Rem = binops::rem(),
            Div = binops::div(),
            Shr = binops::shr(),
            Shl = binops::shl(),
            LogicalAnd = binops::logical_op_and(),
            LogicalOr = binops::logical_op_or(),
        }

        #[derive_group_for_ast]
        /// The names corresponding to callable items of arity 2
        pub enum TernaryName {
        }
    }
}
pub use fun_app::*;

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
