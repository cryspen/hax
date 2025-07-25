//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use crate::ast::span::Span;
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

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Item {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        self.kind.pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b ItemKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            ItemKind::Fn {
                name,
                generics: _,
                body,
                params,
                safety: _,
            } => {
                // Generics are ignored for now
                docs![
                    allocator,
                    "def ",
                    name,
                    allocator.softline(),
                    allocator
                        .intersperse(params, allocator.line())
                        .align()
                        .group(),
                    docs![allocator, allocator.line(), ": ", &body.ty].group(),
                    " :=",
                    allocator.line(),
                    docs![allocator, &*body.kind].group()
                ]
                .nest(INDENT)
                .group()
            }
            ItemKind::TyAlias {
                name,
                generics: _,
                ty,
            } => docs![allocator, "abbrev ", name, allocator.reflow(" := "), ty].group(),
            ItemKind::Type {
                name: _,
                generics: _,
                variants: _,
                is_struct: _,
            } => print_todo!(allocator),
            ItemKind::Trait {
                name: _,
                generics: _,
                items: _,
            } => print_todo!(allocator),
            ItemKind::Impl {
                generics: _,
                self_ty: _,
                of_trait: _,
                items: _,
                parent_bounds: _,
                safety: _,
            } => print_todo!(allocator),
            ItemKind::Alias { name: _, item: _ } => print_todo!(allocator),
            ItemKind::Use {
                path: _,
                is_external: _,
                rename: _,
            } => allocator.nil(),
            ItemKind::Quote {
                quote: _,
                origin: _,
            } => print_todo!(allocator),
            ItemKind::Error(_diagnostic) => print_todo!(allocator),
            ItemKind::Resugared(_resugared_ty_kind) => print_todo!(allocator),
            ItemKind::NotImplementedYet => allocator.text("-- unimplemented yet"),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Ty {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        self.kind().pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b TyKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            TyKind::Primitive(primitive_ty) => primitive_ty.pretty(allocator),
            TyKind::Tuple(items) => allocator.intersperse(items, allocator.reflow(" * ")),
            TyKind::App { head, args } => {
                if args.len() == 0 {
                    head.pretty(allocator)
                } else {
                    head.pretty(allocator)
                        .append(allocator.softline())
                        .append(allocator.intersperse(args, allocator.softline()))
                        .group()
                        .parens()
                }
            }
            TyKind::Arrow { inputs, output } => allocator
                .intersperse(
                    inputs.into_iter().chain(once(output)),
                    allocator.softline().append("-> "),
                )
                .parens(),
            TyKind::Ref {
                inner: _,
                mutable: _,
                region: _,
            } => print_todo!(allocator),
            TyKind::Param(local_id) => local_id.pretty(allocator),
            TyKind::Slice(ty) => docs![allocator, "Array ", ty].parens(),
            TyKind::Array { ty, length } => {
                docs![allocator, "Vector ", ty, allocator.softline(), &(**length),]
                    .parens()
                    .group()
            }
            TyKind::RawPointer => print_todo!(allocator),
            TyKind::AssociatedType { impl_: _, item: _ } => print_todo!(allocator),
            TyKind::Opaque(_global_id) => print_todo!(allocator),
            TyKind::Dyn(_dyn_trait_goals) => print_todo!(allocator),
            TyKind::Resugared(_resugared_ty_kind) => print_todo!(allocator),
            TyKind::Error(_diagnostic) => print_todo!(allocator),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b SpannedTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        self.ty.pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b PrimitiveTy {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            PrimitiveTy::Bool => allocator.text("Bool"),
            PrimitiveTy::Int(int_kind) => int_kind.pretty(allocator),
            PrimitiveTy::Float(float_kind) => float_kind.pretty(allocator),
            PrimitiveTy::Char => allocator.text("Char"),
            PrimitiveTy::Str => allocator.text("String"),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Expr {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        (*self.kind).pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Pat {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        (self.kind).pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b PatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            PatKind::Wild => allocator.text("_"),
            PatKind::Ascription { pat, ty } => {
                docs![allocator, pat, allocator.softline(), ": ", ty]
                    .nest(INDENT)
                    .group()
            }
            PatKind::Or { sub_pats: _ } => print_todo!(allocator),
            PatKind::Array { args: _ } => print_todo!(allocator),
            PatKind::Deref { sub_pat: _ } => print_todo!(allocator),
            PatKind::Constant { lit: _ } => print_todo!(allocator),
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
                constructor: _,
                is_record: _,
                is_struct: _,
                fields: _,
            } => print_todo!(allocator),
            PatKind::Resugared(_resugared_pat_kind) => print_todo!(allocator),
            PatKind::Error(_diagnostic) => print_todo!(allocator),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Lhs {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        print_todo!(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b ExprKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
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
                generic_args: _,
                bounds_impls: _,
                trait_: _,
            } => {
                let separator = allocator.line();
                head.pretty(allocator)
                    .append(allocator.softline())
                    .append(allocator.intersperse(args, separator).nest(INDENT))
                    .parens()
                    .group()
            }
            ExprKind::Literal(literal) => literal.pretty(allocator),
            ExprKind::Array(exprs) => docs![
                allocator,
                "#[",
                allocator
                    .intersperse(exprs, allocator.text(",").append(allocator.line()))
                    .nest(INDENT),
                "]"
            ]
            .group(),
            ExprKind::Construct {
                constructor,
                is_record: _,
                is_struct: _,
                fields,
                base: _,
            } => {
                // Should be turned into a resugaring once https://github.com/cryspen/hax/pull/1528 have been merged
                let record_args = if fields.len() > 0 {
                    Some(
                        allocator.softline().append(
                            allocator
                                .intersperse(
                                    fields.iter().map(|field: &(GlobalId, Expr)| {
                                        docs![
                                            allocator,
                                            &field.0,
                                            " ",
                                            allocator.reflow(":= "),
                                            &field.1
                                        ]
                                        .group()
                                    }),
                                    allocator.reflow(", "),
                                )
                                .group()
                                .braces(),
                        ),
                    )
                } else {
                    None
                };
                docs![allocator, ".constr_", constructor, record_args]
                    .group()
                    .nest(INDENT)
            }
            ExprKind::Match {
                scrutinee: _,
                arms: _,
            } => print_todo!(allocator),
            ExprKind::Tuple(_exprs) => print_todo!(allocator),
            ExprKind::Borrow {
                mutable: _,
                inner: _,
            } => print_todo!(allocator),
            ExprKind::AddressOf {
                mutable: _,
                inner: _,
            } => print_todo!(allocator),
            ExprKind::Deref(_expr) => print_todo!(allocator),
            ExprKind::Let { lhs, rhs, body } => {
                docs![
                    allocator,
                    "let ",
                    lhs,
                    " :=",
                    allocator.softline(),
                    docs![allocator, rhs].group(),
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
            ExprKind::Assign { lhs: _, value: _ } => print_todo!(allocator),
            ExprKind::Loop {
                body: _,
                kind: _,
                state: _,
                control_flow: _,
                label: _,
            } => print_todo!(allocator),
            ExprKind::Break { value: _, label: _ } => print_todo!(allocator),
            ExprKind::Return { value: _ } => print_todo!(allocator),
            ExprKind::Continue { label: _ } => print_todo!(allocator),
            ExprKind::Closure {
                params,
                body,
                captures: _,
            } => docs![
                allocator,
                allocator.reflow("fun "),
                allocator.intersperse(params, allocator.line()),
                allocator.reflow(" =>"),
                allocator.line(),
                body
            ]
            .nest(INDENT)
            .group()
            .parens(),
            ExprKind::Block {
                body: _,
                safety_mode: _,
            } => print_todo!(allocator),
            ExprKind::Quote { contents: _ } => print_todo!(allocator),
            ExprKind::Resugared(_resugared_expr_kind) => print_todo!(allocator),
            ExprKind::Error(_diagnostic) => print_todo!(allocator),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Literal {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        docs![
            allocator,
            match self {
                Literal::String(symbol) => format!("\"{}\"", symbol.to_string()),
                Literal::Char(c) => format!("'{}'", c),
                Literal::Bool(b) => format!("{}", b),
                Literal::Int {
                    value,
                    negative: _,
                    kind: _,
                } => format!("{}", value),
                Literal::Float {
                    value: _,
                    negative: _,
                    kind: _,
                } => todo!(),
            }
        ]
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b IntKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        docs![
            allocator,
            match (&self.size, &self.signedness) {
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
                (IntSize::SSize, Signedness::Signed) => "isize",
                (IntSize::SSize, Signedness::Unsigned) => "usize",
            }
        ]
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b FloatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            FloatKind::F16 => print_todo!(allocator),
            FloatKind::F32 => allocator.text("Float32"),
            FloatKind::F64 => allocator.text("Float"),
            FloatKind::F128 => print_todo!(allocator),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b GenericValue {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            GenericValue::Ty(ty) => ty.pretty(allocator),
            GenericValue::Expr(expr) => expr.pretty(allocator),
            GenericValue::Lifetime => panic!(),
        }
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b LocalId {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        allocator.text(self.to_string())
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b GlobalId {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        allocator.text(self.to_debug_string())
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Param {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        docs![allocator, &self.pat, allocator.softline(), ": ", &self.ty]
            .nest(INDENT)
            .parens()
            .group()
    }
}
