use crate::ast as dst;
use hax_frontend_exporter as src;

use hax_frontend_exporter::ThirBody as Body;

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ErrorKind {
    ParamWithoutPattern,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]

pub struct Error {
    pub span: dst::Span,
    pub kind: ErrorKind,
}

impl ErrorKind {
    fn with_span(self, span: dst::Span) -> Error {
        Error { kind: self, span }
    }
}

type Result<T> = std::result::Result<T, Error>;

fn translate_ty(ty: &src::Ty) -> Result<dst::Ty> {
    Ok(match ty.inner().as_ref() {
        src::TyKind::Bool => dst::Ty::Primitive(dst::PrimitiveTy::Bool),
        src::TyKind::Int(size) => dst::Ty::Primitive(dst::PrimitiveTy::Int(dst::IntKind {
            size: (*size).into(),
            signedness: dst::Signedness::Signed,
        })),
        src::TyKind::Uint(size) => dst::Ty::Primitive(dst::PrimitiveTy::Int(dst::IntKind {
            size: (*size).into(),
            signedness: dst::Signedness::Unsigned,
        })),
        src::TyKind::Ref(_, ty, mutability) => dst::Ty::Ref {
            inner: Box::new(translate_ty(ty)?),
            mutable: *mutability,
        },
        src::TyKind::Tuple(types) => {
            dst::Ty::Tuple(types.iter().map(translate_ty).collect::<Result<_>>()?)
        }
        src::TyKind::Arrow(binder) => dst::Ty::Arrow {
            inputs: binder
                .value
                .inputs
                .iter()
                .map(translate_ty)
                .collect::<Result<_>>()?,
            output: Box::new(translate_ty(&binder.value.output)?),
        },
        src::TyKind::Slice(ty) => dst::Ty::App {
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref())?)],
        },
        src::TyKind::Array(ty, _constant) => dst::Ty::App {
            // TODO: translate as a slice
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref())?)],
        },
        ty => unimplemented!("{ty:?}"),
    })
}
fn translate_pat(pat: &src::Pat) -> Result<dst::Pat> {
    let kind = match pat.contents.as_ref() {
        src::PatKind::Binding { var, .. } => dst::PatKind::Binding {
            mutable: false,
            var: var.into(),
            mode: dst::BindingMode::ByValue,
        },
        _ => unimplemented!(),
    };
    let ty = translate_ty(&pat.ty)?;
    let meta = dst::Metadata {
        span: (&pat.span).into(),
        attrs: translate_attributes(&pat.attributes[..]),
    };
    Ok(dst::Pat { kind, ty, meta })
}
fn translate_param(param: &src::Param, span: dst::Span) -> Result<dst::Param> {
    Ok(dst::Param {
        pat: translate_pat(
            param
                .pat
                .as_ref()
                .ok_or(ErrorKind::ParamWithoutPattern.with_span(span))?,
        )?,
        ty: dst::SpannedTy {
            ty: translate_ty(&param.ty)?,
            span: param.ty_span.as_ref().map(Into::into).unwrap_or(span),
        },
        attributes: vec![],
    })
}
fn translate_expr(expr: &src::Expr) -> Result<dst::Expr> {
    let span = (&expr.span).into();
    let ty = translate_ty(&expr.ty)?;
    let kind = match expr.contents.as_ref() {
        src::ExprKind::Literal { lit, neg } => dst::ExprKind::Literal(match lit.node {
            src::LitKind::Bool(bool) => dst::Literal::Bool(bool),
            src::LitKind::Int(value, _) => match &ty {
                dst::Ty::Primitive(dst::PrimitiveTy::Int(kind)) => dst::Literal::Int {
                    value,
                    negative: *neg,
                    kind: kind.clone(),
                },
                _ => unimplemented!(),
            },
            _ => unimplemented!(),
        }),
        src::ExprKind::GlobalName { id, .. } => dst::ExprKind::GlobalId(id.clone().into()),
        src::ExprKind::PointerCoercion { source, .. } => return translate_expr(&source),
        src::ExprKind::Array { fields } => {
            dst::ExprKind::Array(fields.iter().map(translate_expr).collect::<Result<_>>()?)
        }
        src::ExprKind::Call { fun, args, .. } => {
            // let ty = translate_ty(ty)?;
            let head = translate_expr(fun)?;
            let args = args
                .iter()
                .map(translate_expr)
                .collect::<Result<Vec<_>>>()?;
            dst::ExprKind::App { head, args }
        }
        src::ExprKind::Borrow {
            borrow_kind: src::BorrowKind::Shared,
            arg,
        } => dst::ExprKind::Borrow {
            mutable: false,
            inner: translate_expr(arg)?,
        },
        src::ExprKind::Deref { arg } => dst::ExprKind::Deref(translate_expr(arg)?),
        src::ExprKind::VarRef { id } => dst::ExprKind::LocalId(id.into()),
        src::ExprKind::Block {
            block: src::Block { stmts, expr, .. },
        } => {
            let mut terminator = expr.as_ref().map(translate_expr).unwrap_or_else(|| {
                let kind = dst::ExprKind::Tuple(vec![]);
                Ok(dst::Expr {
                    kind: Box::new(kind),
                    ty,
                    meta: dst::Metadata {
                        span,
                        attrs: vec![],
                    },
                })
            })?;
            for src::Stmt { kind: stmt } in stmts.iter().rev() {
                let (lhs, rhs) = match stmt {
                    src::StmtKind::Let {
                        pattern: lhs,
                        initializer: Some(rhs),
                        ..
                    } => (translate_pat(lhs)?, translate_expr(rhs)?),
                    src::StmtKind::Expr { expr, .. } => {
                        let rhs = translate_expr(expr)?;
                        (
                            dst::Pat {
                                kind: dst::PatKind::Wild,
                                ty: rhs.ty.clone(),
                                meta: dst::Metadata {
                                    attrs: vec![],
                                    ..rhs.meta
                                },
                            },
                            rhs,
                        )
                    }
                    _ => unimplemented!(),
                };
                let ty = terminator.ty.clone();
                let kind = dst::ExprKind::Let {
                    lhs,
                    rhs,
                    body: terminator,
                };
                terminator = dst::Expr {
                    kind: Box::new(kind),
                    ty,
                    meta: dst::Metadata {
                        span,
                        attrs: vec![],
                    },
                }
            }
            return Ok(terminator);
        }
        c => unimplemented!("{c:?}"),
    };
    Ok(dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attrs: vec![],
        },
    })
}
fn translate_attributes(_attributes: &[src::Attribute]) -> Vec<dst::Attribute> {
    vec![]
}

pub fn translate_item(item: &src::Item<Body>) -> Result<dst::Item> {
    let span = (&item.span).into();
    let kind = match &item.kind {
        src::ItemKind::Fn(_generics, fn_def) => dst::ItemKind::Fn {
            name: (&item.owner_id).clone().into(),
            generics: dst::Generics,
            body: translate_expr(&fn_def.body)?,
            params: fn_def
                .params
                .iter()
                .map(|param| translate_param(param, span))
                .collect::<Result<_>>()?,
            safety: dst::SafetyKind::Safe,
        },
        _ => unimplemented!(),
    };
    Ok(dst::Item {
        ident: item.owner_id.clone().into(),
        kind,
        meta: dst::Metadata {
            span,
            attrs: translate_attributes(&item.attributes.attributes[..]),
        },
    })
}

#[test]
fn import_json() {
    let items: Vec<hax_frontend_exporter::Item<Body>> =
        serde_json::from_str(include_str!("../test.json")).unwrap();

    println!("type Slice<T> = [T];");
    let printer = crate::printer::rust::RustPrinter;
    for src in &items {
        let i = translate_item(src).unwrap();

        use crate::printer::Printer;
        println!("{}", printer.item(&i));
    }
}
