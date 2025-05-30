//! Pretty-printer traits and implementations for AST structures.
//!
//! This module provides the `Printer` trait and a default `RustPrinter` that
//! converts AST nodes back to Rust-like syntax as strings.

// TODO: revisit, take time to think about it
// Here, the goal is to handle spans, errors and AST positions automatically.
// We also want to be able to pretty print, not just print.
// We need also a dispatch mechanism.

use crate::ast::*;

pub type Doc = String;

pub trait Printer {
    fn item_kind(&self, item_kind: &ItemKind) -> Doc;
    fn attribute(&self, attribute: &Attribute) -> Doc;
    fn attributes(&self, attributes: &Attributes) -> Doc;
    fn item(&self, item: &Item) -> Doc;
    fn expr_kind(&self, expr_kind: &ExprKind) -> Doc;
    fn literal(&self, literal: &Literal) -> Doc;
    fn generic_value(&self, generic_value: &GenericValue) -> Doc;
    fn ty(&self, ty: &Ty) -> Doc;
    fn pat_kind(&self, pat_kind: &PatKind) -> Doc;
    fn param(&self, param: &Param) -> Doc;
}

pub trait ToDoc<P: Printer> {
    fn to_doc(&self, printer: &P) -> Doc;
}

impl<P: Printer> ToDoc<P> for Literal {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.literal(self)
    }
}
impl<P: Printer> ToDoc<P> for Ty {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.ty(self)
    }
}
impl<P: Printer> ToDoc<P> for PatKind {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.pat_kind(self)
    }
}
impl<P: Printer> ToDoc<P> for ExprKind {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.expr_kind(self)
    }
}
impl<P: Printer> ToDoc<P> for Attribute {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.attribute(self)
    }
}
impl<P: Printer> ToDoc<P> for Attributes {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.attributes(self)
    }
}
impl<P: Printer> ToDoc<P> for ItemKind {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.item_kind(self)
    }
}
impl<P: Printer> ToDoc<P> for Item {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.item(self)
    }
}
impl<P: Printer> ToDoc<P> for Param {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.param(self)
    }
}
impl<P: Printer> ToDoc<P> for GlobalId {
    fn to_doc(&self, _printer: &P) -> Doc {
        self.to_string()
    }
}
impl<P: Printer> ToDoc<P> for LocalId {
    fn to_doc(&self, _printer: &P) -> Doc {
        self.0.to_string()
    }
}
impl<P: Printer> ToDoc<P> for GenericValue {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.generic_value(self)
    }
}
impl<P: Printer> ToDoc<P> for Expr {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.expr_kind(self.kind())
    }
}
impl<P: Printer> ToDoc<P> for Pat {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.pat_kind(self.kind())
    }
}
impl<P: Printer> ToDoc<P> for SpannedTy {
    fn to_doc(&self, printer: &P) -> Doc {
        printer.ty(self.ty())
    }
}

impl<P: Printer, T: ToDoc<P>> ToDoc<P> for Box<T> {
    fn to_doc(&self, printer: &P) -> Doc {
        self.as_ref().to_doc(printer)
    }
}

impl std::fmt::Display for IntSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                Self::S8 => "8",
                Self::S16 => "16",
                Self::S32 => "32",
                Self::S64 => "64",
                Self::S128 => "128",
                Self::SSize => "size",
            }
        )
    }
}

impl std::fmt::Display for Signedness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                Signedness::Signed => "i",
                Signedness::Unsigned => "u",
            },
        )
    }
}
impl std::fmt::Display for IntKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}{}", &self.signedness, &self.size)
    }
}

pub mod rust {
    use super::*;
    pub struct RustPrinter;

    impl Printer for RustPrinter {
        fn item_kind(&self, item: &ItemKind) -> Doc {
            match item {
                ItemKind::Fn {
                    name,
                    generics: _,
                    body,
                    params,
                    safety: _,
                } => {
                    format!(
                        r#"pub fn {}({}) -> {} {{ {} }}"#,
                        name.name(),
                        params
                            .iter()
                            .map(|param| param.to_doc(self))
                            .collect::<Vec<_>>()
                            .join(","),
                        body.ty().to_doc(self),
                        body.to_doc(self),
                    )
                }
                ItemKind::Error(_) => "<item error>".to_string(),
            }
        }
        fn attribute(&self, _item: &Attribute) -> Doc {
            todo!()
        }
        fn attributes(&self, _item: &Attributes) -> Doc {
            todo!()
        }
        fn item(&self, item: &Item) -> Doc {
            item.kind.to_doc(self)
        }
        fn expr_kind(&self, expr_kind: &ExprKind) -> Doc {
            match &expr_kind {
                ExprKind::Let { lhs, rhs, body } => {
                    format!(
                        "let {} = {};\n{}",
                        lhs.to_doc(self),
                        rhs.to_doc(self),
                        body.to_doc(self)
                    )
                }
                ExprKind::GlobalId(global_id) => global_id.to_string(),
                ExprKind::LocalId(local_id) => local_id.to_string(),
                ExprKind::Deref(inner) => format!("*{}", inner.to_doc(self)),
                ExprKind::Borrow { mutable, inner } => format!(
                    "&{}{}",
                    if *mutable { "mut " } else { "" },
                    inner.to_doc(self)
                ),
                ExprKind::Array(values) => {
                    format!(
                        "[{}]",
                        values
                            .iter()
                            .map(|e| e.to_doc(self))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                ExprKind::Tuple(values) => {
                    format!(
                        "({})",
                        values
                            .iter()
                            .map(|e| e.to_doc(self))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                ExprKind::App { head, args } => {
                    let args = args
                        .iter()
                        .map(|expr| expr.to_doc(self))
                        .collect::<Vec<_>>();
                    let f = head.to_doc(self);
                    match (head.kind.as_ref(), &args[..]) {
                        (ExprKind::GlobalId(hd), [lhs, index]) if hd == &GlobalId::index() => {
                            format!("({lhs})[{index}]")
                        }
                        _ => format!("({f})({})", args.join(",")),
                    }
                }
                ExprKind::Literal(lit) => lit.to_doc(self),
                &ExprKind::If {
                    condition,
                    then_,
                    else_,
                } => {
                    format!(
                        "if {} {{ {} }} {}",
                        condition.to_doc(self),
                        then_.to_doc(self),
                        else_
                            .as_ref()
                            .map(|e| format!(" else {{ {} }}", e.to_doc(self)))
                            .unwrap_or(Doc::default())
                    )
                }
                ExprKind::Error(_) => "<expression error>".to_string(),
            }
        }
        fn literal(&self, lit: &Literal) -> Doc {
            match lit {
                Literal::Bool(b) => b.to_string(),
                Literal::Char(c) => format!("'{}'", c),
                Literal::Float { .. } => "todo".to_string(),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => format!("{}{value}{}", if *negative { "-" } else { "" }, kind),
                Literal::String(s) => s.to_string(),
            }
        }
        fn generic_value(&self, generic_value: &GenericValue) -> Doc {
            match generic_value {
                GenericValue::Ty(ty) => ty.to_doc(self),
                GenericValue::Expr(expr) => expr.to_doc(self),
            }
        }
        fn ty(&self, ty: &Ty) -> Doc {
            match ty {
                Ty::Primitive(PrimitiveTy::Bool) => "bool".to_string(),
                Ty::Primitive(PrimitiveTy::Int(int_kind)) => int_kind.to_string(),
                Ty::Tuple(tys) => format!(
                    "({})",
                    tys.iter()
                        .map(|ty| ty.to_doc(self))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Ty::App { head, args } => {
                    let args = args.iter().map(|arg| arg.to_doc(self)).collect::<Vec<_>>();
                    match &args[..] {
                        [inner] if head == &GlobalId::slice() => format!("[{inner}]"),
                        _ => format!("{}<{}>", head.to_doc(self), args.join(", ")),
                    }
                }
                Ty::Arrow { inputs, output } => {
                    let inputs = inputs
                        .iter()
                        .map(|input| format!("{} -> ", input.to_doc(self)))
                        .collect::<Vec<_>>()
                        .join("");
                    let output = output.to_doc(self);
                    format!("{}{}", inputs, output)
                }
                Ty::Ref { inner, mutable } => {
                    let mutability = if *mutable {
                        "mut".to_string()
                    } else {
                        Doc::default()
                    };
                    format!("&{}{}", mutability, inner.to_doc(self))
                }
                Ty::Error(_) => "<type error>".to_string(),
            }
        }
        fn pat_kind(&self, pat: &PatKind) -> Doc {
            match pat {
                PatKind::Wild => "_".to_string(),
                PatKind::Binding { mutable, var, mode } => {
                    format!(
                        "{} {}{}",
                        if *mutable { "mut" } else { "" },
                        var.to_doc(self),
                        match mode {
                            BindingMode::ByValue => "",
                            BindingMode::ByRef(BorrowKind::Mut) => "&mut",
                            BindingMode::ByRef(_) => "&",
                        }
                    )
                }
                PatKind::Error(_) => "<pattern error>".to_string(),
            }
        }
        fn param(&self, param: &Param) -> Doc {
            format!("{}: {}", param.pat.to_doc(self), param.ty.to_doc(self))
        }
    }
}
