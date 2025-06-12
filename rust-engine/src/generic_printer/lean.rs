use crate::ast::{node::NodeRef, GlobalId, IntKind, Literal};

use super::doc_printer::print;
use super::{doc_printer::*, print_context::*, print_view::*, to_print_view::*};
use pretty::*;

use crate::ast;

pub(crate) const INDENT: isize = 2;

macro_rules! todo {
    () => {
        RcDoc::text("[TODO]")
    };
}

pub struct LeanPrinter;

impl Printer for LeanPrinter {
    fn resugar_expr(_e: crate::ast::Expr) -> Option<super::resugar::ResugaredExprKind> {
        None
    }
}
impl<'a: 'p, 'p> ToDoc<'a, 'p, GenericValue<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: GenericValue<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        match x {
            GenericValue::Ty(ty) => print(ty, self),
            GenericValue::Expr(e) => print(e, self),
            GenericValue::Lifetime => panic!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, SpannedTy<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: SpannedTy<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        print(x.ty, self)
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Ty<'a>> for LeanPrinter {
    fn to_doc(&'p self, ty: Ty<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        match ty {
            Ty::Primitive(prim) => print(prim, self),
            Ty::Tuple(print_context) => panic!(),
            Ty::App { head, args } => RcDoc::text(head.to_string())
                .append(" ")
                .append(RcDoc::intersperse(
                    args.open().into_iter().map(|arg| print(arg, self)),
                    RcDoc::softline(),
                ))
                .group(),
            Ty::Arrow { inputs, output } => panic!(),
            Ty::Ref {
                inner,
                mutable,
                region,
            } => panic!(),
            Ty::Param(print_context) => RcDoc::text("param"),
            Ty::Slice(print_context) => panic!(),
            Ty::Array { ty, length } => panic!(),
            Ty::RawPointer => panic!(),
            Ty::AssociatedType { impl_, item } => RcDoc::text("associated"),
            Ty::Opaque(print_context) => RcDoc::text("opaque"),
            Ty::Dyn(print_context) => panic!(),
            Ty::Error(print_context) => panic!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, PrimitiveTy<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: PrimitiveTy<'a>,
        _context: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<()> {
        match x {
            PrimitiveTy::Bool => RcDoc::text("Bool"),
            PrimitiveTy::Int(int) => {
                let int_val: IntKind = int.value.to_owned();
                self.to_doc(int_val, int.payload)
            }
            PrimitiveTy::Float(print_context) => panic!(),
            PrimitiveTy::Char => panic!(),
            PrimitiveTy::Str => panic!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, IntKind> for LeanPrinter {
    fn to_doc(&'p self, x: IntKind, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        match (x.size, x.signedness) {
            (ast::IntSize::S8, ast::Signedness::Signed) => panic!(),
            (ast::IntSize::S8, ast::Signedness::Unsigned) => panic!(),
            (ast::IntSize::S16, ast::Signedness::Signed) => panic!(),
            (ast::IntSize::S16, ast::Signedness::Unsigned) => panic!(),
            (ast::IntSize::S32, ast::Signedness::Signed) => RcDoc::text("i32"),
            (ast::IntSize::S32, ast::Signedness::Unsigned) => panic!(),
            (ast::IntSize::S64, ast::Signedness::Signed) => RcDoc::text("i64"),
            (ast::IntSize::S64, ast::Signedness::Unsigned) => panic!(),
            (ast::IntSize::S128, ast::Signedness::Signed) => panic!(),
            (ast::IntSize::S128, ast::Signedness::Unsigned) => panic!(),
            (ast::IntSize::SSize, ast::Signedness::Signed) => panic!(),
            (ast::IntSize::SSize, ast::Signedness::Unsigned) => panic!(),
        }
    }
}

// impl<'a> ToDoc<'a, Box<T>>

impl<'a: 'p, 'p> ToDoc<'a, 'p, Expr<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: Expr<'a>,
        _context: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<'p, ()> {
        let value: &ast::ExprKind = &*x.kind.value;
        print(
            PrintContext {
                value: value,
                payload: x.kind.payload,
            },
            self,
        )
    }
}

impl<'a> ToPrintView<'a> for Literal {
    type Out = Self;
    fn to_print_view(
        &'a self,
        _parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        self.clone()
    }
}

impl<'a> Into<NodeRef<'a>> for &Literal {
    fn into(self) -> NodeRef<'a> {
        NodeRef::Literal
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, ExprKind<'a>> for LeanPrinter {
    fn to_doc(
        &'p self,
        x: ExprKind<'a>,
        p: super::print_context::PrintContextPayload<'a>,
    ) -> RcDoc<'p, ()> {
        match x {
            ExprKind::If {
                condition,
                then,
                else_,
            } => match else_.value {
                Some(else_branch) => RcDoc::group(
                    RcDoc::text("if")
                        .append(RcDoc::softline())
                        .append(RcDoc::nest(print(condition, self), 1))
                        .append(RcDoc::softline())
                        .append(RcDoc::text("then"))
                        .append(RcDoc::softline())
                        .append(RcDoc::nest(print(then, self), 1))
                        .append(RcDoc::softline())
                        .append(RcDoc::text(" else "))
                        .append(RcDoc::softline())
                        .append(print(
                            PrintContext {
                                value: else_branch,
                                payload: else_.payload,
                            },
                            self,
                        )),
                ),
                None => panic!(),
            },
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => RcDoc::text("(")
                .append(print(head, self))
                .append(RcDoc::softline())
                .append(RcDoc::intersperse(
                    args.open().into_iter().map(|arg| print(arg, self)),
                    RcDoc::softline(),
                ))
                .append(")")
                .nest(INDENT)
                .group(),
            ExprKind::Literal(print_context) => print(print_context, self),
            ExprKind::Array(print_context) => panic!(),
            ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            } => panic!(),
            ExprKind::Match { scrutinee, arms } => panic!(),
            ExprKind::Tuple(print_context) => panic!(),
            ExprKind::Borrow { mutable, inner } => panic!(),
            ExprKind::AddressOf { mutability, inner } => panic!(),
            ExprKind::Deref(print_context) => panic!(),
            ExprKind::Let { lhs, rhs, body } => RcDoc::group(
                RcDoc::text("let ")
                    .append(print(lhs, self))
                    .append(" := ")
                    .append(print(rhs, self))
                    .append(" ;")
                    .append(RcDoc::hardline())
                    .append(print(body, self)),
            ),
            ExprKind::GlobalId(gid) => RcDoc::text(gid.value.to_string()),
            ExprKind::LocalId(lid) => RcDoc::text(lid.value.to_string()),
            ExprKind::Ascription { e, ty } => panic!(),
            ExprKind::Assign { lhs, value } => panic!(),
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => panic!(),
            ExprKind::Break { value, label } => panic!(),
            ExprKind::Return { value } => panic!(),
            ExprKind::Continue { label } => panic!(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => panic!(),
            ExprKind::Block { body, safety_mode } => match safety_mode.value {
                ast::SafetyKind::Safe => RcDoc::group(print(body, self)),
                ast::SafetyKind::Unsafe => panic!(),
            },
            ExprKind::Quote { contents } => panic!(),
            ExprKind::Error(print_context) => panic!(),
        }
    }
}

impl<'a: 'p, 'p, T> ToDoc<'a, 'p, Box<T>> for LeanPrinter
where
    LeanPrinter: ToDoc<'a, 'p, T>,
{
    fn to_doc(&'p self, x: Box<T>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        self.to_doc(*x, p)
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Pat<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: Pat<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        let kind = x.kind;
        print(kind, self)
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, PatKind<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: PatKind<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        match x {
            PatKind::Wild => panic!(),
            PatKind::Ascription { ty, typ_span, pat } => panic!(),
            PatKind::Or { sub_pats } => panic!(),
            PatKind::Array { args } => panic!(),
            PatKind::Deref { sub_pat } => panic!(),
            PatKind::Constant { lit } => panic!(),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => match (mutable.value, mode.value, sub_pat.value) {
                (false, ast::BindingMode::ByValue, None) => RcDoc::text(var.value.to_string()),
                _ => panic!(),
            },
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => panic!(),
            PatKind::Error(print_context) => panic!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Literal> for LeanPrinter {
    fn to_doc(&self, x: Literal, p: super::print_context::PrintContextPayload<'a>) -> RcDoc<()> {
        match x {
            Literal::String(symbol) => panic!(),
            Literal::Char(_) => panic!(),
            Literal::Bool(true) => RcDoc::text("true"),
            Literal::Bool(false) => RcDoc::text("false"),
            Literal::Int {
                value,
                negative,
                kind,
            } => RcDoc::text(format!("{}", value)),
            Literal::Float {
                value,
                negative,
                kind,
            } => panic!(),
        }
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Item<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: Item<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        print(x.kind, self)
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, GlobalId> for LeanPrinter {
    fn to_doc(&'p self, x: GlobalId, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        RcDoc::text(x.to_string())
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, Param<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: Param<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        RcDoc::text("(")
            .append(print(x.pat, self))
            .append(RcDoc::softline())
            .append(":")
            .append(RcDoc::softline())
            .append(print(x.ty, self))
            .append(")")
    }
}

impl<'a: 'p, 'p> ToDoc<'a, 'p, ItemKind<'a>> for LeanPrinter {
    fn to_doc(&'p self, x: ItemKind<'a>, p: PrintContextPayload<'a>) -> RcDoc<'p, ()> {
        match x {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let name = self.to_doc(name.value.clone(), name.payload);
                let params: Vec<PrintContext<_>> = params.open();
                let args = match params[..] {
                    [] => RcDoc::text(""),
                    _ => RcDoc::softline().append(
                        RcDoc::intersperse(
                            params.into_iter().map(|param| print(param, self)),
                            RcDoc::line(),
                        )
                        .nest(INDENT)
                        .group(),
                    ),
                };
                RcDoc::concat([
                    RcDoc::text("def "),
                    name,
                    args,
                    RcDoc::softline(),
                    RcDoc::text(":"),
                    RcDoc::softline(),
                    print(body.value.to_print_view(None).ty, self),
                    RcDoc::text(":="),
                    RcDoc::line(),
                    print(body, self),
                ])
                .nest(INDENT)
                .group()
            }
            ItemKind::TyAlias { name, generics, ty } => RcDoc::text("def ")
                .append(RcDoc::text(name.value.to_string()))
                .append(RcDoc::text(" : Type := "))
                .append(print(ty, self)),
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => panic!(),
            ItemKind::Trait {
                name,
                generics,
                items,
            } => panic!(),
            ItemKind::Impl {
                generics,
                self_ty,
                of_trait,
                items,
                parent_bounds,
                safety,
            } => panic!(),
            ItemKind::Alias { name, item } => panic!(),
            ItemKind::Use {
                path,
                is_external,
                rename,
            } => RcDoc::text("-- [todo] use "),
            ItemKind::Quote { quote, origin } => panic!(),
            ItemKind::Error(print_context) => panic!(),
            ItemKind::NotImplementedYet => RcDoc::text("-- non implemented yet"),
        }
    }
}
