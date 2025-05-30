//! Logic for translating frontend representations into the internal AST.
//!
//! It handles fallbacks for unsupported constructs by emitting `Diagnostic` errors.

use crate::ast as dst;
use crate::ast::diagnostics::*;
use hax_frontend_exporter as src;

use hax_frontend_exporter::ThirBody as Body;

fn translate_ty(ty: &src::Ty, span: dst::Span) -> dst::Ty {
    let translate_ty = |ty| translate_ty(ty, span);
    match ty.inner().as_ref() {
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
            inner: Box::new(translate_ty(ty)),
            mutable: *mutability,
        },
        src::TyKind::Tuple(types) => dst::Ty::Tuple(types.iter().map(translate_ty).collect()),
        src::TyKind::Arrow(binder) => dst::Ty::Arrow {
            inputs: binder.value.inputs.iter().map(translate_ty).collect(),
            output: Box::new(translate_ty(&binder.value.output)),
        },
        src::TyKind::Slice(ty) => dst::Ty::App {
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref()))],
        },
        src::TyKind::Array(ty, _constant) => dst::Ty::App {
            // TODO: translate as a slice
            head: dst::GlobalId::slice(),
            args: vec![dst::GenericValue::Ty(translate_ty(ty.as_ref()))],
        },
        ty => dst::Ty::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: ty: {ty:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    }
}
fn translate_pat(pat: &src::Pat) -> dst::Pat {
    let span = (&pat.span).into();
    let kind = match pat.contents.as_ref() {
        src::PatKind::Wild => dst::PatKind::Wild,
        src::PatKind::Binding { var, .. } => dst::PatKind::Binding {
            mutable: false,
            var: var.into(),
            mode: dst::BindingMode::ByValue,
        },
        pat => dst::PatKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: pat: {pat:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    };
    let ty = translate_ty(&pat.ty, span);
    let meta = dst::Metadata {
        span,
        attrs: translate_attributes(&pat.attributes),
    };
    dst::Pat { kind, ty, meta }
}
fn translate_param(param: &src::Param, span: dst::Span) -> Result<dst::Param, DiagnosticInfo> {
    Ok(dst::Param {
        pat: translate_pat(param.pat.as_ref().ok_or(DiagnosticInfo {
            context: Context::Import,
            span,
            kind: DiagnosticInfoKind::ImportParamWithoutPattern,
        })?),
        ty: dst::SpannedTy {
            ty: translate_ty(&param.ty, span),
            span: param.ty_span.as_ref().map(Into::into).unwrap_or(span),
        },
        attributes: vec![],
    })
}
fn translate_expr(expr: &src::Expr) -> dst::Expr {
    let span = (&expr.span).into();
    let ty = translate_ty(&expr.ty, span);
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
        src::ExprKind::Index { lhs, index } => {
            let head = dst::Expr {
                kind: Box::new(dst::ExprKind::GlobalId(dst::GlobalId::index())),
                ty: ty.clone(),
                meta: dst::Metadata {
                    span,
                    attrs: vec![],
                },
            };
            let args = vec![translate_expr(lhs), translate_expr(index)];
            dst::ExprKind::App { head, args }
        }
        src::ExprKind::GlobalName { id, .. } => dst::ExprKind::GlobalId(id.clone().into()),
        src::ExprKind::PointerCoercion { source, .. } => return translate_expr(source),
        src::ExprKind::Array { fields } => {
            dst::ExprKind::Array(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Call { fun, args, .. } => {
            let head = translate_expr(fun);
            let args = args.iter().map(translate_expr).collect::<Vec<_>>();
            dst::ExprKind::App { head, args }
        }
        src::ExprKind::Borrow {
            borrow_kind: src::BorrowKind::Shared,
            arg,
        } => dst::ExprKind::Borrow {
            mutable: false,
            inner: translate_expr(arg),
        },
        src::ExprKind::Tuple { fields } => {
            dst::ExprKind::Tuple(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Deref { arg } => dst::ExprKind::Deref(translate_expr(arg)),
        src::ExprKind::VarRef { id } => dst::ExprKind::LocalId(id.into()),
        src::ExprKind::Block {
            block: src::Block { stmts, expr, .. },
        } => {
            let mut terminator = expr.as_ref().map(translate_expr).unwrap_or_else(|| {
                let kind = dst::ExprKind::Tuple(vec![]);
                dst::Expr {
                    kind: Box::new(kind),
                    ty,
                    meta: dst::Metadata {
                        span,
                        attrs: vec![],
                    },
                }
            });
            for src::Stmt { kind: stmt } in stmts.iter().rev() {
                let (lhs, rhs) = match stmt {
                    src::StmtKind::Let {
                        pattern: lhs,
                        initializer: Some(rhs),
                        ..
                    } => (translate_pat(lhs), translate_expr(rhs)),
                    src::StmtKind::Expr { expr, .. } => {
                        let rhs = translate_expr(expr);
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
            return terminator;
        }
        expr => dst::ExprKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: expr: {expr:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    };
    dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attrs: vec![],
        },
    }
}
fn translate_attributes(_attributes: &[src::Attribute]) -> Vec<dst::Attribute> {
    vec![]
}

pub fn translate_item_kind(
    item_kind: &src::ItemKind<Body>,
    name: dst::GlobalId,
    span: dst::Span,
) -> dst::ItemKind {
    match item_kind {
        src::ItemKind::Fn(_generics, fn_def) => {
            let params = fn_def
                .params
                .iter()
                .map(|param| translate_param(param, span))
                .collect::<Result<_, _>>();
            let params = match params {
                Ok(params) => params,
                Err(diag_info) => {
                    return dst::ItemKind::Error(Diagnostic::new(
                        dst::Node::Unknown(format!("Rust THIR: param in function <{name:?}>")),
                        diag_info,
                    ))
                }
            };
            dst::ItemKind::Fn {
                name,
                generics: dst::Generics,
                body: translate_expr(&fn_def.body),
                params,
                safety: dst::SafetyKind::Safe,
            }
        }
        _ => dst::ItemKind::Error(Diagnostic::new(
            dst::Node::Unknown(format!("Rust THIR: item: {item_kind:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    }
}

pub fn translate_item(item: &src::Item<Body>) -> dst::Item {
    let span = (&item.span).into();
    let name: dst::GlobalId = item.owner_id.clone().into();
    let kind = translate_item_kind(&item.kind, name.clone(), span);
    dst::Item {
        ident: name,
        kind,
        meta: dst::Metadata {
            span,
            attrs: translate_attributes(&item.attributes.attributes[..]),
        },
    }
}
