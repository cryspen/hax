//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use crate::ast::span::Span;
use crate::printer::Allocator;

use pretty::{DocAllocator, DocBuilder, Pretty, docs};

use crate::ast::identifiers::*;
use crate::ast::literals::*;
use crate::ast::*;

macro_rules! print_todo {
    ($allocator:ident) => {
        $allocator
            .text(format!(
                "/- Unsupported by the Lean Backend (line {}) -/",
                line!()
            ))
            .parens()
    };
}

const INDENT: isize = 2;

/// Placeholder structure for lean printer
pub struct Lean;

impl Lean {
    /// A filter for items blacklisted by the Lean backend : returns false if
    /// the item is definitely not printable, but might return true on
    /// unsupported items
    pub fn printable_item(item: &Item) -> bool {
        match &item.kind {
            // Anonymous consts
            ItemKind::Fn {
                name,
                generics: _,
                body: _,
                params: _,
                safety: _,
            } if name.is_empty() => false,
            // Other unprintable items
            ItemKind::Error(_) | ItemKind::NotImplementedYet | ItemKind::Use { .. } => false,
            // Printable items
            ItemKind::Fn { .. }
            | ItemKind::TyAlias { .. }
            | ItemKind::Type { .. }
            | ItemKind::Trait { .. }
            | ItemKind::Impl { .. }
            | ItemKind::Alias { .. }
            | ItemKind::Resugared(_)
            | ItemKind::Quote { .. } => true,
        }
    }
}

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
                generics,
                body,
                params,
                safety: _,
            } => {
                match &*body.kind {
                    ExprKind::Literal(l) => {
                        // Literal consts, printed without monadic encoding
                        // Todo: turn it into a proper refactor (see Hax issue #1542)
                        docs![
                            allocator,
                            "def ",
                            name,
                            allocator.reflow(" : "),
                            &body.ty,
                            allocator.reflow(" :="),
                            allocator.line(),
                            l
                        ]
                        .group()
                    }
                    _ => {
                        // Normal definition
                        let generics = if generics.params.is_empty() {
                            None
                        } else {
                            Some(
                                docs![
                                    allocator,
                                    allocator.line(),
                                    allocator
                                        .intersperse(&generics.params, allocator.softline())
                                        .braces()
                                        .group()
                                ]
                                .group(),
                            )
                        };
                        let args = if params.is_empty() {
                            allocator.nil()
                        } else {
                            docs![
                                allocator,
                                allocator.line(),
                                allocator.intersperse(params, allocator.softline()),
                            ]
                            .nest(INDENT)
                            .group()
                        };
                        docs![
                            allocator,
                            "def ",
                            name,
                            generics,
                            args,
                            docs![
                                allocator,
                                allocator.line(),
                                ": ",
                                docs![allocator, "Result ", &body.ty].group()
                            ]
                            .group(),
                            " := do",
                            allocator.line(),
                            docs![allocator, &*body.kind].group()
                        ]
                        .nest(INDENT)
                        .group()
                        .append(allocator.hardline())
                    }
                }
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
            ItemKind::Quote { quote, origin: _ } => quote.pretty(allocator),
            ItemKind::Error(_diagnostic) => print_todo!(allocator),
            ItemKind::Resugared(_resugared_ty_kind) => print_todo!(allocator),
            ItemKind::NotImplementedYet => allocator.text("/- unsupported by Hax engine (yet) -/"),
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
                        .parens()
                        .group()
                }
            }
            TyKind::Arrow { inputs, output } => docs![
                allocator,
                allocator.concat(inputs.into_iter().map(|input| docs![
                    allocator,
                    input,
                    allocator.reflow(" -> ")
                ])),
                "Result ",
                output
            ]
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
        docs![
            allocator,
            self.kind.pretty(allocator),
            allocator.reflow(" : "),
            &self.ty
        ]
        .parens()
        .group()
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b PatKind {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            PatKind::Wild => allocator.text("_"),
            PatKind::Ascription { pat, ty: _ } => pat.kind.pretty(allocator),
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
                Some(else_branch) => docs![
                    allocator,
                    allocator
                        .text("if")
                        .append(allocator.line())
                        .append(condition)
                        .group(),
                    allocator.line(),
                    allocator
                        .text("then")
                        .append(allocator.line())
                        .append(then)
                        .group()
                        .nest(INDENT),
                    allocator.line(),
                    allocator
                        .text("else")
                        .append(allocator.line())
                        .append(else_branch)
                        .group()
                        .nest(INDENT),
                ]
                .group(),
                None => print_todo!(allocator),
            },
            ExprKind::App {
                head,
                args,
                generic_args: _,
                bounds_impls: _,
                trait_: _,
            } if match &*head.kind {
                ExprKind::GlobalId(name) => {
                    *name == crate::names::rust_primitives::hax::machine_int::add()
                }
                _ => false,
            } && args.len() == 2 =>
            {
                docs![
                    allocator,
                    "← ",
                    args.get(0),
                    allocator.reflow(" +? "),
                    args.get(1),
                ]
                .parens()
                .group()
            }
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls: _,
                trait_: _,
            } => {
                let generic_args = (!generic_args.is_empty()).then_some(
                    allocator
                        .line()
                        .append(
                            allocator
                                .intersperse(generic_args, allocator.line())
                                .nest(INDENT),
                        )
                        .group(),
                );
                let args = if args.is_empty() {
                    None
                } else {
                    Some(
                        allocator
                            .line()
                            .append(allocator.intersperse(args, allocator.line()).nest(INDENT))
                            .group(),
                    )
                };
                docs![allocator, "← ", head, generic_args, args]
                    .parens()
                    .group()
            }
            ExprKind::Literal(literal) => literal.pretty(allocator),
            ExprKind::Array(exprs) => docs![
                allocator,
                "#v[",
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
                let record_args = (fields.len() > 0).then_some(
                    allocator
                        .line()
                        .append(
                            allocator
                                .intersperse(
                                    fields.iter().map(|field: &(GlobalId, Expr)| {
                                        docs![
                                            allocator,
                                            &field.0,
                                            allocator.reflow(" := "),
                                            &field.1
                                        ]
                                        .parens()
                                        .group()
                                    }),
                                    allocator.line(),
                                )
                                .group(),
                        )
                        .group(),
                );
                docs![allocator, "constr_", constructor, record_args]
                    .parens()
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
            ExprKind::Let { lhs, rhs, body } => docs![
                allocator,
                "let ",
                lhs,
                " ←",
                allocator.softline(),
                docs![allocator, "pure", allocator.line(), rhs]
                    .group()
                    .nest(INDENT),
                ";",
                allocator.line(),
                body,
            ]
            .group(),
            ExprKind::GlobalId(global_id) => global_id.pretty(allocator),
            ExprKind::LocalId(local_id) => local_id.pretty(allocator),
            ExprKind::Ascription { e, ty } => {
                let monadic_encoding = match *e.kind {
                    ExprKind::Literal(_) | ExprKind::Construct { .. } => None,
                    _ => Some("← "),
                };
                docs![allocator, monadic_encoding, e, allocator.reflow(" : "), ty]
                    .parens()
                    .group()
            }
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
                allocator.intersperse(params, allocator.softline()).group(),
                allocator.reflow("=> do"),
                allocator.line(),
                body
            ]
            .parens()
            .group()
            .nest(INDENT),
            ExprKind::Block {
                body: _,
                safety_mode: _,
            } => print_todo!(allocator),
            ExprKind::Quote { contents } => allocator.concat(&contents.0),
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
        self.pat.pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b GenericParam {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        self.ident.pretty(allocator)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b Quote {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        allocator.concat(&self.0)
    }
}

impl<'a, 'b> Pretty<'a, Allocator<Lean>, Span> for &'b QuoteContent {
    fn pretty(self, allocator: &'a Allocator<Lean>) -> DocBuilder<'a, Allocator<Lean>, Span> {
        match self {
            QuoteContent::Verbatim(s) => {
                allocator.intersperse(s.lines().map(|x| x.to_string()), allocator.hardline())
            }
            QuoteContent::Expr(expr) => expr.pretty(allocator),
            QuoteContent::Pattern(pat) => pat.pretty(allocator),
            QuoteContent::Ty(ty) => ty.pretty(allocator),
        }
    }
}
