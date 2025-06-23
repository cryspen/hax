//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use crate::printer::Allocator;
use pretty::{docs, DocAllocator, DocBuilder, Pretty};

use crate::ast::identifiers::*;
use crate::ast::literals::*;
use crate::ast::*;

macro_rules! print_todo {
    ($allocator:ident) => {
        $allocator.text("Todo")
    };
}

const INDENT: isize = 2;

/// Placeholder structure for lean printer
pub struct Lean;

/// Implementations for each part of the AST

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Item {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        self.kind.pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for ItemKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => todo!(),
            ItemKind::TyAlias { name, generics, ty } => todo!(),
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => todo!(),
            ItemKind::Trait {
                name,
                generics,
                items,
            } => todo!(),
            ItemKind::Impl {
                generics,
                self_ty,
                of_trait,
                items,
                parent_bounds,
                safety,
            } => todo!(),
            ItemKind::Alias { name, item } => todo!(),
            ItemKind::Use {
                path,
                is_external,
                rename,
            } => todo!(),
            ItemKind::Quote { quote, origin } => todo!(),
            ItemKind::Error(diagnostic) => todo!(),
            ItemKind::Resugared(resugared_ty_kind) => todo!(),
            ItemKind::NotImplementedYet => todo!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Ty {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for TyKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            TyKind::Primitive(primitive_ty) => todo!(),
            TyKind::Tuple(items) => todo!(),
            TyKind::App { head, args } => todo!(),
            TyKind::Arrow { inputs, output } => todo!(),
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => todo!(),
            TyKind::Param(local_id) => todo!(),
            TyKind::Slice(ty) => todo!(),
            TyKind::Array { ty, length } => todo!(),
            TyKind::RawPointer => todo!(),
            TyKind::AssociatedType { impl_, item } => todo!(),
            TyKind::Opaque(global_id) => todo!(),
            TyKind::Dyn(dyn_trait_goals) => todo!(),
            TyKind::Resugared(resugared_ty_kind) => todo!(),
            TyKind::Error(diagnostic) => todo!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for SpannedTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for PrimitiveTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Expr {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        (*self.kind).pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Pat {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for PatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Lhs {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        todo!()
    }
}

impl<'a, A: 'a + Clone + Clone> Pretty<'a, Allocator<Lean>, A> for ExprKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            ExprKind::If {
                condition,
                then,
                else_,
            } => match else_ {
                Some(else_branch) => allocator
                    .concat([
                        allocator.text("if"),
                        allocator.softline().append(condition).nest(INDENT),
                        allocator.line().append("then"),
                        allocator.softline().append(then).nest(INDENT),
                        allocator.line().append("else"),
                        allocator.softline().append(else_branch).nest(INDENT),
                    ])
                    .group(),
                None => todo!(),
            },
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let separator = allocator.softline();
                head.pretty(allocator)
                    .append(allocator.softline())
                    .append(allocator.intersperse(args, separator))
                    .parens()
            }
            ExprKind::Literal(literal) => literal.pretty(allocator),
            ExprKind::Array(exprs) => todo!(),
            ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            } => todo!(),
            ExprKind::Match { scrutinee, arms } => todo!(),
            ExprKind::Tuple(exprs) => todo!(),
            ExprKind::Borrow { mutable, inner } => todo!(),
            ExprKind::AddressOf { mutable, inner } => todo!(),
            ExprKind::Deref(expr) => todo!(),
            ExprKind::Let { lhs, rhs, body } => todo!(),
            ExprKind::GlobalId(global_id) => todo!(),
            ExprKind::LocalId(local_id) => todo!(),
            ExprKind::Ascription { e, ty } => todo!(),
            ExprKind::Assign { lhs, value } => todo!(),
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => todo!(),
            ExprKind::Break { value, label } => todo!(),
            ExprKind::Return { value } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => todo!(),
            ExprKind::Block { body, safety_mode } => todo!(),
            ExprKind::Quote { contents } => todo!(),
            ExprKind::Resugared(resugared_expr_kind) => todo!(),
            ExprKind::Error(diagnostic) => todo!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Literal {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            Literal::String(symbol) => todo!(),
            Literal::Char(_) => todo!(),
            Literal::Bool(_) => todo!(),
            Literal::Int {
                value,
                negative,
                kind,
            } => todo!(),
            Literal::Float {
                value,
                negative,
                kind,
            } => todo!(),
        }
    }
}
