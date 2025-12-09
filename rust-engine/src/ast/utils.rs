//! This module defines helper methods or items to construct or destruct the AST.

use super::*;

impl Expr {
    /// Create a tuple expression out of components.
    pub fn tuple(components: Vec<Expr>, span: Span) -> Self {
        let ty = TyKind::tuple(
            components
                .iter()
                .map(Typed::ty)
                .cloned()
                .map(GenericValue::Ty)
                .collect(),
        )
        .promote();
        ExprKind::tuple(components).promote(ty, span)
    }

    /// Creates a `App` node for a standalone function.
    pub fn standalone_fn_app(
        head: impl Into<FnAppHead>,
        generic_args: Vec<GenericValue>,
        args: Vec<Expr>,
        output_type: Ty,
        span: Span,
    ) -> Self {
        ExprKind::standalone_fn_app(head, generic_args, args, output_type.clone(), span)
            .promote(output_type, span)
    }

    /// Creates a `App` node.
    pub fn fn_app(
        head: impl Into<FnAppHead>,
        generic_args: Vec<GenericValue>,
        args: Vec<Expr>,
        output_type: Ty,
        bounds_impls: Vec<ImplExpr>,
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
        span: Span,
    ) -> Self {
        ExprKind::fn_app(
            head,
            generic_args,
            args,
            output_type.clone(),
            bounds_impls,
            trait_,
            span,
        )
        .promote(output_type, span)
    }
}

impl ExprKind {
    /// Creates a `App` node for a standalone function.
    pub fn standalone_fn_app(
        head: impl Into<FnAppHead>,
        generic_args: Vec<GenericValue>,
        args: Vec<Expr>,
        output_type: Ty,
        span: Span,
    ) -> Self {
        Self::fn_app(head, generic_args, args, output_type, vec![], None, span)
    }

    /// Creates a `App` node.
    pub fn fn_app(
        head: impl Into<FnAppHead>,
        generic_args: Vec<GenericValue>,
        args: Vec<Expr>,
        output_type: Ty,
        bounds_impls: Vec<ImplExpr>,
        trait_: Option<(ImplExpr, Vec<GenericValue>)>,
        span: Span,
    ) -> Self {
        let head = 'head: {
            let kind = match head.into() {
                FnAppHead::GlobalId(global_id) => ExprKind::GlobalId(global_id),
                FnAppHead::ExprKind(expr_kind) => expr_kind,
                FnAppHead::Expr(expr) => break 'head expr,
            };
            let head_ty = TyKind::Arrow {
                inputs: args.iter().map(Typed::ty).cloned().collect(),
                output: output_type.clone(),
            }
            .promote();
            kind.promote(head_ty, span)
        };

        Self::App {
            head,
            args,
            generic_args,
            bounds_impls,
            trait_,
        }
    }

    /// Creates a tuple out of a vector of components.
    pub fn tuple(components: Vec<Expr>) -> Self {
        let length = components.len();
        ExprKind::Construct {
            constructor: global_id::TupleId::Constructor { length }.into(),
            is_record: false,
            is_struct: true,
            fields: components
                .into_iter()
                .enumerate()
                .map(|(field, expr)| (global_id::TupleId::Field { length, field }.into(), expr))
                .collect(),
            base: None,
        }
    }

    /// Promote to an `Expr`
    pub fn promote(self, ty: Ty, span: Span) -> Expr {
        Expr {
            kind: Box::new(self),
            ty,
            meta: Metadata {
                span,
                attributes: Vec::new(),
            },
        }
    }
}

/// Helper enum that describes what can serve as function application heads.
/// This is an helper that is useful for [`ExprKind::fn_application`].
pub enum FnAppHead {
    /// A global identifier
    GlobalId(GlobalId),
    /// An expression kind
    ExprKind(ExprKind),
    /// A full blown expression
    Expr(Expr),
}

impl From<GlobalId> for FnAppHead {
    fn from(value: GlobalId) -> Self {
        Self::GlobalId(value)
    }
}
impl From<ExprKind> for FnAppHead {
    fn from(value: ExprKind) -> Self {
        Self::ExprKind(value)
    }
}
impl From<Expr> for FnAppHead {
    fn from(value: Expr) -> Self {
        Self::Expr(value)
    }
}

impl Generics {
    /// Concatenate two generics
    pub fn concat(mut self, other: Self) -> Self {
        self.constraints.extend(other.constraints);
        self.params.extend(other.params);
        use std::cmp::Ordering;
        self.params.sort_by(|a, b| match (a.kind(), b.kind()) {
            (GenericParamKind::Lifetime, GenericParamKind::Lifetime) => Ordering::Equal,
            (GenericParamKind::Lifetime, _) => Ordering::Less,
            (_, GenericParamKind::Lifetime) => Ordering::Greater,
            _ => Ordering::Equal,
        });
        self
    }
    /// Empty generics
    pub fn empty() -> Self {
        Self {
            params: Vec::new(),
            constraints: Vec::new(),
        }
    }
}

impl ItemKind {
    /// Promote to an item
    pub fn promote(self, ident: GlobalId, span: Span) -> Item {
        Item {
            ident,
            kind: self,
            meta: Metadata {
                span,
                attributes: Vec::new(),
            },
        }
    }
}

impl GenericValue {
    /// Tries to extract a [`Ty`] out of a [`GenericValue`].
    pub fn expect_ty(&self) -> Option<&Ty> {
        let Self::Ty(ty) = self else { return None };
        Some(ty)
    }
}

impl TyKind {
    /// Tuple type
    pub fn tuple(args: Vec<GenericValue>) -> Self {
        let head = global_id::TupleId::Type { length: args.len() }.into();
        Self::App { head, args }
    }
    /// Unit type
    pub fn unit() -> Self {
        Self::tuple(Vec::new())
    }
    /// Promote to a Ty
    pub fn promote(self) -> Ty {
        Ty(Box::new(self))
    }
}

impl Arm {
    /// Create a non-guarded arm
    pub fn non_guarded(pat: Pat, body: Expr, span: Span) -> Self {
        Self {
            pat,
            body,
            guard: None,
            meta: Metadata {
                span,
                attributes: Vec::new(),
            },
        }
    }
}

impl PatKind {
    /// Pattern for binding to a single variable
    pub fn var_pat(var: LocalId) -> Self {
        Self::Binding {
            mutable: false,
            var,
            mode: BindingMode::ByValue,
            sub_pat: None,
        }
    }
    /// Promote to a `Pat`
    pub fn promote(self, ty: Ty, span: Span) -> Pat {
        Pat {
            kind: Box::new(self),
            ty,
            meta: Metadata {
                span,
                attributes: Vec::new(),
            },
        }
    }
}

impl Variant {
    /// Whether a variant has fields or not.
    /// See https://doc.rust-lang.org/reference/items/enumerations.html#field-less-enum.
    pub fn is_fieldless(&self) -> bool {
        self.arguments.is_empty()
    }
}
