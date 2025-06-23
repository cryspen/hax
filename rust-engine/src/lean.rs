//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use crate::printer::Allocator;
use std::iter::once;

use pretty::{docs, DocAllocator, DocBuilder, Pretty};

use crate::ast::identifiers::*;
use crate::ast::literals::*;
use crate::ast::*;

macro_rules! print_todo {
    ($allocator:ident) => {
        $allocator.text(format!("Todo at {}", line!())).parens()
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
            } => {
                if !(generics.params.is_empty()
                    && generics.constraints.is_empty()
                    && safety == SafetyKind::Safe)
                {
                    panic!()
                };
                docs![
                    allocator,
                    "def",
                    allocator.softline(),
                    name,
                    allocator.softline(),
                    allocator
                        .intersperse(params, allocator.softline())
                        .nest(INDENT)
                        .group(),
                    allocator.reflow(" : "),
                    body.ty,
                    allocator.reflow(" :="),
                    allocator.line(),
                    *body.kind,
                ]
                .nest(INDENT)
                .group()
            }
            ItemKind::TyAlias { name, generics, ty } => {
                docs![allocator, "def ", name, allocator.reflow(" : Type := "), ty].group()
            }
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => print_todo!(allocator),
            ItemKind::Trait {
                name,
                generics,
                items,
            } => print_todo!(allocator),
            ItemKind::Impl {
                generics,
                self_ty,
                of_trait,
                items,
                parent_bounds,
                safety,
            } => print_todo!(allocator),
            ItemKind::Alias { name, item } => print_todo!(allocator),
            ItemKind::Use {
                path,
                is_external,
                rename,
            } => allocator.text("-- use statement [unsupported]"),
            ItemKind::Quote { quote, origin } => print_todo!(allocator),
            ItemKind::Error(diagnostic) => print_todo!(allocator),
            ItemKind::Resugared(resugared_ty_kind) => print_todo!(allocator),
            ItemKind::NotImplementedYet => allocator.text("-- unimplemented yet"),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Ty {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        self.0.pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for TyKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            TyKind::Primitive(primitive_ty) => primitive_ty.pretty(allocator),
            TyKind::Tuple(items) => allocator.intersperse(items, allocator.reflow(" * ")),
            TyKind::App { head, args } => head
                .pretty(allocator)
                .append(allocator.softline())
                .append(allocator.intersperse(args, allocator.softline()))
                .parens(),
            TyKind::Arrow { inputs, output } => allocator
                .intersperse(
                    inputs.into_iter().chain(once(output)),
                    allocator.reflow(" -> "),
                )
                .parens(),
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => print_todo!(allocator),
            TyKind::Param(local_id) => print_todo!(allocator),
            TyKind::Slice(ty) => print_todo!(allocator),
            TyKind::Array { ty, length } => print_todo!(allocator),
            TyKind::RawPointer => print_todo!(allocator),
            TyKind::AssociatedType { impl_, item } => print_todo!(allocator),
            TyKind::Opaque(global_id) => print_todo!(allocator),
            TyKind::Dyn(dyn_trait_goals) => print_todo!(allocator),
            TyKind::Resugared(resugared_ty_kind) => print_todo!(allocator),
            TyKind::Error(diagnostic) => panic!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for SpannedTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        self.ty.pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for PrimitiveTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            PrimitiveTy::Bool => allocator.text("Bool"),
            PrimitiveTy::Int(int_kind) => int_kind.pretty(allocator),
            PrimitiveTy::Float(float_kind) => float_kind.pretty(allocator),
            PrimitiveTy::Char => allocator.text("Char"),
            PrimitiveTy::Str => allocator.text("String"),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Expr {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        (*self.kind).pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Pat {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        self.kind.pretty(allocator)
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for PatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            PatKind::Wild => print_todo!(allocator),
            PatKind::Ascription { pat, ty } => todo!(),
            PatKind::Or { sub_pats } => todo!(),
            PatKind::Array { args } => todo!(),
            PatKind::Deref { sub_pat } => todo!(),
            PatKind::Constant { lit } => todo!(),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => match (mutable, mode, sub_pat) {
                (false, BindingMode::ByValue, None) => var.pretty(allocator),
                _ => panic!(),
            },
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => todo!(),
            PatKind::Resugared(resugared_pat_kind) => todo!(),
            PatKind::Error(diagnostic) => todo!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Lhs {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        print_todo!(allocator)
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
                None => print_todo!(allocator),
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
            ExprKind::Array(exprs) => print_todo!(allocator),
            ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            } => print_todo!(allocator),
            ExprKind::Match { scrutinee, arms } => print_todo!(allocator),
            ExprKind::Tuple(exprs) => print_todo!(allocator),
            ExprKind::Borrow { mutable, inner } => print_todo!(allocator),
            ExprKind::AddressOf { mutable, inner } => print_todo!(allocator),
            ExprKind::Deref(expr) => print_todo!(allocator),
            ExprKind::Let { lhs, rhs, body } => {
                docs![
                    allocator,
                    "let ",
                    lhs,
                    allocator.reflow(" := "),
                    docs![allocator, rhs].nest(INDENT).group(),
                    ";",
                    allocator.line(),
                    body,
                ]
            }
            ExprKind::GlobalId(global_id) => global_id.pretty(allocator),
            ExprKind::LocalId(local_id) => local_id.pretty(allocator),
            ExprKind::Ascription { e, ty } => docs![allocator, e, allocator.reflow(" : "), ty]
                .nest(INDENT)
                .parens()
                .group(),
            ExprKind::Assign { lhs, value } => print_todo!(allocator),
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => print_todo!(allocator),
            ExprKind::Break { value, label } => print_todo!(allocator),
            ExprKind::Return { value } => print_todo!(allocator),
            ExprKind::Continue { label } => print_todo!(allocator),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => print_todo!(allocator),
            ExprKind::Block { body, safety_mode } => print_todo!(allocator),
            ExprKind::Quote { contents } => print_todo!(allocator),
            ExprKind::Resugared(resugared_expr_kind) => print_todo!(allocator),
            ExprKind::Error(diagnostic) => print_todo!(allocator),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Literal {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        docs![
            allocator,
            match self {
                Literal::String(symbol) => format!("\"{}\"", symbol.to_string()),
                Literal::Char(c) => format!("'{}'", c),
                Literal::Bool(b) => format!("{}", b),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => format!("{}", value),
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => todo!(),
            }
        ]
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for IntKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        docs![
            allocator,
            match (self.size, self.signedness) {
                (IntSize::S8, Signedness::Signed) => "i8",
                (IntSize::S8, Signedness::Unsigned) => "u8",
                (IntSize::S16, Signedness::Signed) => "i16",
                (IntSize::S16, Signedness::Unsigned) => "u16",
                (IntSize::S32, Signedness::Signed) => "i32",
                (IntSize::S32, Signedness::Unsigned) => "u32",
                (IntSize::S64, Signedness::Signed) => "i64",
                (IntSize::S64, Signedness::Unsigned) => "u64",
                (IntSize::S128, Signedness::Signed) => "i128",
                (IntSize::S128, Signedness::Unsigned) => "u128",
                (IntSize::SSize, Signedness::Signed) => todo!(),
                (IntSize::SSize, Signedness::Unsigned) => todo!(),
            }
        ]
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for FloatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            FloatKind::F16 => print_todo!(allocator),
            FloatKind::F32 => allocator.text("Float32"),
            FloatKind::F64 => allocator.text("Float"),
            FloatKind::F128 => print_todo!(allocator),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for GenericValue {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        match self {
            GenericValue::Ty(ty) => ty.pretty(allocator),
            GenericValue::Expr(expr) => expr.pretty(allocator),
            GenericValue::Lifetime => panic!(),
        }
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for LocalId {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        allocator.text(self.to_string())
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for GlobalId {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        allocator.text(self.to_debug_string())
    }
}

impl<'a, A: 'a + Clone> Pretty<'a, Allocator<Lean>, A> for Params {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, A> {
        docs![allocator, self.pat, allocator.reflow(" : "), self.ty]
            .nest(INDENT)
            .parens()
            .group()
    }
}
