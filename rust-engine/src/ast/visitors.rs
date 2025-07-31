//! This module provides various visitors for the AST of hax.
//!
//! - VisitEarlyExit
//! - VisitMapDiag
//! - VisitMap

use super::*;
use derive_generic_visitor::*;

mod wrappers {
    use std::ops::Deref;

    use super::{infaillible::AstVisitable as AstVisitableInfaillible, *};
    use diagnostics::*;

    /// A visitor wrapper that provides span information.
    pub struct SpanWrapper<'a, V>(pub &'a mut V);

    impl<'a, V: HasSpan> SpanWrapper<'a, V> {
        fn spanned_action<T: Deref, U>(&mut self, x: T, action: impl Fn(&mut Self, T) -> U) -> U
        where
            T::Target: HasSpan,
        {
            let span_before = self.0.span();
            *self.0.span_mut() = x.span();
            let result = action(self, x);
            *self.0.span_mut() = span_before;
            result
        }
    }

    impl<'a, V: AstVisitorMut + HasSpan> AstVisitorMut for SpanWrapper<'a, V> {
        fn visit_inner<T>(&mut self, x: &mut T)
        where
            T: AstVisitableInfaillible,
            T: for<'s> DriveMut<'s, AstVisitableInfaillibleWrapper<Self>>,
        {
            x.drive_map(self.0)
        }
        fn visit_item(&mut self, x: &mut Item) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_expr(&mut self, x: &mut Expr) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_pat(&mut self, x: &mut Pat) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_guard(&mut self, x: &mut Guard) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_arm(&mut self, x: &mut Arm) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_impl_item(&mut self, x: &mut ImplItem) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_trait_item(&mut self, x: &mut TraitItem) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_generic_param(&mut self, x: &mut GenericParam) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_attribute(&mut self, x: &mut Attribute) {
            self.spanned_action(x, Self::visit_inner)
        }
        fn visit_spanned_ty(&mut self, x: &mut SpannedTy) {
            self.spanned_action(x, Self::visit_inner)
        }
    }

    /// A visitor wrapper that automatically collects errors in `ErrorNode`s.
    pub struct ErrorWrapper<'a, V>(pub &'a mut V);
    #[derive(Default)]
    pub struct ErrorVault(Vec<Diagnostic>);
    impl ErrorVault {
        fn add(&mut self, diagnostic: Diagnostic) {
            self.0.push(diagnostic);
        }
    }

    pub struct ErrorHandlingState(pub Span, pub ErrorVault);
    impl Default for ErrorHandlingState {
        fn default() -> Self {
            Self(Span::dummy(), Default::default())
        }
    }

    pub trait VisitorWithContext {
        fn context(&self) -> Context;
    }

    impl<T: HasSpan> HasSpan for ErrorWrapper<'_, T> {
        fn span(&self) -> Span {
            self.0.span()
        }

        fn span_mut(&mut self) -> &mut Span {
            self.0.span_mut()
        }
    }

    pub trait VisitorWithErrors: HasSpan + VisitorWithContext {
        fn error_vault(&mut self) -> &mut ErrorVault;
        fn error(&mut self, node: impl Into<Fragment>, kind: DiagnosticInfoKind) {
            let context = self.context();
            let span = self.span();
            self.error_vault().add(Diagnostic::new(
                node,
                DiagnosticInfo {
                    context,
                    span,
                    kind,
                },
            ));
        }
    }

    impl<'a, V: VisitorWithErrors> ErrorWrapper<'a, V> {
        fn error_handled_action<T: HasErrorNode + Clone + std::fmt::Debug + Into<Fragment>, U>(
            &mut self,
            x: &mut T,
            action: impl Fn(&mut Self, &mut T) -> U,
        ) -> U {
            let diagnostics_snapshot = self.0.error_vault().0.clone();
            self.0.error_vault().0.clear();
            let result = action(self, x);
            let diagnostics: Vec<_> = self.0.error_vault().0.drain(..).collect();
            if !diagnostics.is_empty() {
                x.set_error(ErrorNode {
                    fragment: Box::new(x.clone().into()),
                    diagnostics,
                });
            }
            self.0.error_vault().0 = diagnostics_snapshot;
            result
        }
    }

    impl<'a, V: AstVisitorMut + VisitorWithErrors> AstVisitorMut for ErrorWrapper<'a, V> {
        fn visit_inner<T>(&mut self, x: &mut T)
        where
            T: AstVisitableInfaillible,
            T: for<'s> DriveMut<'s, AstVisitableInfaillibleWrapper<Self>>,
        {
            x.drive_map(self.0)
        }
        fn visit_item(&mut self, x: &mut Item) {
            self.error_handled_action(x, Self::visit_inner)
        }
        fn visit_pat(&mut self, x: &mut Pat) {
            self.error_handled_action(x, Self::visit_inner)
        }
        fn visit_expr(&mut self, x: &mut Expr) {
            self.error_handled_action(x, Self::visit_inner)
        }
        fn visit_ty(&mut self, x: &mut Ty) {
            self.error_handled_action(x, Self::visit_inner)
        }
    }
}

#[macro_export]
/// Use this macro in an implementation of `AstVisitorMut` to get automatic spans and error handling.
macro_rules! setup_error_handling {
    () => {
        fn visit<'a, T: $crate::ast::visitors::infaillible::AstVisitable>(&'a mut self, x: &mut T) {
            $crate::ast::visitors::wrappers::SpanWrapper(
                &mut $crate::ast::visitors::wrappers::ErrorWrapper(self),
            )
            .visit(x)
        }
    };
}

pub use setup_error_handling;
mod infaillible {
    use super::*;
    use diagnostics::*;
    use identifiers::*;
    use literals::*;
    use resugared::*;
    use span::*;

    #[visitable_group(
        visitor(drive_map(
            /// An mutable visitor that visits the AST for hax.
            &mut AstVisitorMut
        ), infaillible),
        visitor(drive(
            /// An immutable visitor that visits the AST for hax.
            &AstVisitor
        ), infaillible),
        skip(
            String, bool, char, hax_frontend_exporter::Span,
        ),
        drive(
            for<T: AstVisitable> Box<T>, for<T: AstVisitable> Option<T>, for<T: AstVisitable> Vec<T>,
            for<A: AstVisitable, B: AstVisitable> (A, B),
            for<A: AstVisitable, B: AstVisitable, C: AstVisitable> (A, B, C),
            usize
        ),
        override(
            Expr, Pat, ExprKind, PatKind, Ty, TyKind, Metadata, Literal,
            LocalId, Lhs, Symbol, LoopKind, SafetyKind, Quote,
            SpannedTy, BindingMode, PrimitiveTy, Region, ImplExpr,
            IntKind, FloatKind, GenericValue, Arm, LoopState, ControlFlowKind,
            DynTraitGoal, Attribute, QuoteContent, BorrowKind,
            TraitGoal, ImplExprKind, IntSize, Signedness, Guard, AttributeKind,
            GuardKind, ImplItem, ImplItemKind, TraitItem, TraitItemKind,
            ItemQuoteOrigin, ItemQuoteOriginKind, ItemQuoteOriginPosition, GenericParamKind, ImplIdent,
            ProjectionPredicate, GenericParam, Generics, DocCommentKind, Param, Variant, ItemKind, Item,
            GenericConstraint, ErrorNode,

            ResugaredExprKind, ResugaredTyKind, ResugaredPatKind,
            ResugaredImplItemKind, ResugaredTraitItemKind, ResugaredItemKind
        ),
        override_skip(
            Span, Fragment, GlobalId, Diagnostic,
        ),
    )]
    pub trait AstVisitable {}
}
#[allow(missing_docs)]
mod faillible {
    use super::*;
    use diagnostics::*;
    use identifiers::*;
    use literals::*;
    use resugared::*;
    use span::*;

    #[visitable_group(
        visitor(drive(
            /// An immutable visitor that can exit early.
            &VisitEarlyExit
        )),
        skip(
            String, bool, char, hax_frontend_exporter::Span,
        ),
        drive(
            for<T: AstVisitable> Box<T>, for<T: AstVisitable> Option<T>, for<T: AstVisitable> Vec<T>,
            for<A: AstVisitable, B: AstVisitable> (A, B),
            for<A: AstVisitable, B: AstVisitable, C: AstVisitable> (A, B, C),
            usize
        ),
        override(
            Expr, Pat, ExprKind, PatKind, Ty, TyKind, Metadata, Literal,
            LocalId, Lhs, Symbol, LoopKind, SafetyKind, Quote,
            SpannedTy, BindingMode, PrimitiveTy, Region, ImplExpr,
            IntKind, FloatKind, GenericValue, Arm, LoopState, ControlFlowKind,
            DynTraitGoal, Attribute, QuoteContent, BorrowKind,
            TraitGoal, ImplExprKind, IntSize, Signedness, Guard, AttributeKind,
            GuardKind, ImplItem, ImplItemKind, TraitItem, TraitItemKind,
            ItemQuoteOrigin, ItemQuoteOriginKind, ItemQuoteOriginPosition, GenericParamKind, ImplIdent,
            ProjectionPredicate, GenericParam, Generics, DocCommentKind, Param, Variant, ItemKind, Item,
            GenericConstraint, ErrorNode,

            ResugaredExprKind, ResugaredTyKind, ResugaredPatKind,
            ResugaredImplItemKind, ResugaredTraitItemKind, ResugaredItemKind
        ),
        override_skip(
            Span, Fragment, GlobalId, Diagnostic,
        ),
    )]
    pub trait AstVisitable {}
}

pub use faillible::{AstVisitableWrapper, VisitEarlyExit};
pub use infaillible::{AstVisitableInfaillibleWrapper, AstVisitor, AstVisitorMut};
pub use wrappers::{VisitorWithContext, VisitorWithErrors};

#[test]
fn double_literals_in_ast() {
    use crate::ast::diagnostics::*;

    #[hax_rust_engine_macros::setup_derive_handling]
    #[derive(Default)]
    struct DoubleU8Literals;

    impl VisitorWithContext for DoubleU8Literals {
        fn context(&self) -> Context {
            Context::Import
        }
    }

    impl AstVisitorMut for DoubleU8Literals {
        setup_error_handling!();

        fn visit_literal(&mut self, x: &mut Literal) {
            let Literal::Int { value, .. } = x else {
                return;
            };
            let Ok(n): Result<u8, _> = str::parse(value) else {
                return self.error(
                    x.clone(),
                    DiagnosticInfoKind::AssertionFailure {
                        details: "Bad literal".into(),
                    },
                );
            };
            let n = (n as u16) * 2;
            if n >= u8::MAX as u16 {
                return self.error(
                    x.clone(),
                    DiagnosticInfoKind::AssertionFailure {
                        details: "Literal too big".into(),
                    },
                );
            }
            *value = Symbol::new(&format!("{}", n));
        }
    }

    // Syntax helpers
    let int_kind = IntKind {
        size: IntSize::S8,
        signedness: Signedness::Signed,
    };
    let mk_lit = |n: isize| Literal::Int {
        value: Symbol::new(&format!("{}", n)),
        negative: false,
        kind: int_kind.clone(),
    };
    let meta = Metadata {
        span: Span::dummy(),
        attributes: vec![],
    };
    let mk_lit_expr = |n| Expr {
        kind: Box::new(ExprKind::Literal(mk_lit(n))),
        ty: Ty(Box::new(TyKind::Primitive(PrimitiveTy::Int(
            int_kind.clone(),
        )))),
        meta: meta.clone(),
    };
    let mk_tuple = |exprs| Expr {
        kind: Box::new(ExprKind::Tuple(exprs)),
        ty: Ty(Box::new(TyKind::RawPointer)), // wrong type, but this is not important for this test.
        meta: meta.clone(),
    };
    let mut lit_expr_200 = mk_lit_expr(200);

    // Creates the expression `[50u8, 100u8, 200u8]`: the last one cannot be doubled, and will cause an error.
    let mut e = mk_tuple(vec![
        mk_lit_expr(50),
        mk_lit_expr(100),
        lit_expr_200.clone(),
    ]);

    // Visit the expression.
    DoubleU8Literals::default().visit(&mut e);

    // Transform `lit_expr_200` into the error `DoubleU8Literal` should produce
    lit_expr_200.set_error(ErrorNode {
        fragment: Box::new(lit_expr_200.clone().into()),
        diagnostics: vec![Diagnostic::new(
            mk_lit(200),
            DiagnosticInfo {
                span: lit_expr_200.span(),
                context: Context::Import,
                kind: DiagnosticInfoKind::AssertionFailure {
                    details: "Literal too big".into(),
                },
            },
        )],
    });

    // Check that the visitor works as expected
    assert_eq!(
        e,
        mk_tuple(vec![mk_lit_expr(100), mk_lit_expr(200), lit_expr_200])
    );
}
