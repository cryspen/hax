//! Logic for translating frontend representations into the internal AST.
//!
//! It handles fallbacks for unsupported constructs by emitting `Diagnostic` errors.

// TODO: this file is stale. We keep it just to keep typecheckable by Rust. We will reuse most of this file later.
#![allow(unused)]

use crate::ast::{self as dst, GenericValue, GlobalId, LocalId};
use crate::ast::{diagnostics::*, GenericParamKind};
use hax_frontend_exporter::{
    self as src, ConstantExprKind, ConstantInt, ConstantLiteral, Decorated, GenericArg,
};

use hax_frontend_exporter::ThirBody as Body;
use hax_types::cli_options::Glob;

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
            region: dst::Region,
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
        src::TyKind::Param(param_ty) => dst::Ty::Param((&(*param_ty.name)).into()),
        src::TyKind::Adt {
            generic_args,
            def_id,
            ..
        } => dst::Ty::App {
            head: def_id.clone().into(),
            args: translate_generic_args(generic_args, span),
        },
        ty => dst::Ty::Error(Diagnostic::new(
            dst::Fragment::Unknown(format!("Rust THIR: ty: {ty:?}")),
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
    let kind = Box::new(match pat.contents.as_ref() {
        src::PatKind::Wild => dst::PatKind::Wild,
        src::PatKind::Binding { var, .. } => todo!()/* dst::PatKind::Binding {
            mutable: false,
            var: var.into(),
            mode: dst::BindingMode::ByValue,
        } */,
        src::PatKind::Tuple { .. } => todo!()/* dst::PatKind::Construct {
            constructor: GlobalId::tuple_pat(),
            is_record: false,
            is_struct: true,
            fields: sub_patterns
                .iter()
                .enumerate()
                .map(|(i, p)| (GlobalId::tuple_field(i), translate_pat(p)))
                .collect(),
        } */,
        pat => dst::PatKind::Error(Diagnostic::new(
            dst::Fragment::Unknown(format!("Rust THIR: pat: {pat:?}")),
            DiagnosticInfo {
                context: Context::Import,
                span,
                kind: DiagnosticInfoKind::Custom("Unimplemented".to_string()),
            },
        )),
    });
    let ty = translate_ty(&pat.ty, span);
    let meta = dst::Metadata {
        span,
        attributes: translate_attributes(&pat.attributes),
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
fn translate_generic_arg(generic_arg: &GenericArg, span: dst::Span) -> GenericValue {
    match generic_arg {
        GenericArg::Lifetime(region) => GenericValue::Lifetime,
        GenericArg::Type(ty) => GenericValue::Ty(translate_ty(ty, span)),
        GenericArg::Const(c_expr) => GenericValue::Expr(translate_constant_expr(c_expr)),
    }
}
fn translate_generic_args(generic_args: &Vec<GenericArg>, span: dst::Span) -> Vec<GenericValue> {
    generic_args
        .iter()
        .map(|generic_arg| translate_generic_arg(generic_arg, span))
        .collect()
}
fn translate_int_literal(ty: &dst::Ty, value: u128, negative: bool) -> dst::Literal {
    match ty {
        dst::Ty::Primitive(dst::PrimitiveTy::Int(kind)) => dst::Literal::Int {
            value,
            negative,
            kind: kind.clone(),
        },
        _ => unimplemented!(),
    }
}
fn translate_constant_expr(c_expr: &Decorated<ConstantExprKind>) -> dst::Expr {
    let span = (&c_expr.span).into();
    let ty = translate_ty(&c_expr.ty, span);
    let kind = match c_expr.contents.as_ref() {
        ConstantExprKind::Literal(lit) => dst::ExprKind::Literal(match lit {
            ConstantLiteral::Bool(bool) => dst::Literal::Bool(*bool),
            ConstantLiteral::Int(ConstantInt::Int(value, _)) => {
                translate_int_literal(&ty, i128::abs(*value) as u128, *value < 0)
            }
            ConstantLiteral::Int(ConstantInt::Uint(value, _)) => {
                translate_int_literal(&ty, *value, false)
            }
            _ => unimplemented!(),
        }),
        ConstantExprKind::Adt { info, fields } => unimplemented!(),
        ConstantExprKind::Array { fields } => unimplemented!(),
        ConstantExprKind::Tuple { fields } => unimplemented!(),
        ConstantExprKind::GlobalName {
            id,
            generics,
            trait_refs,
        } => unimplemented!(),
        _ => unimplemented!(),
    };
    dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attributes: vec![],
        },
    }
}
fn unit_expr(span: dst::Span) -> dst::Expr {
    dst::Expr {
        kind: Box::new(dst::ExprKind::Tuple(Vec::new())),
        ty: dst::Ty::Tuple(Vec::new()),
        meta: dst::Metadata {
            span,
            attributes: vec![],
        },
    }
}
fn translate_expr(expr: &src::Expr) -> dst::Expr {
    let span = (&expr.span).into();
    let ty = translate_ty(&expr.ty, span);
    let kind = match expr.contents.as_ref() {
        src::ExprKind::Box { value } => dst::helper::simple_app(
            GlobalId::box_new(),
            vec![translate_expr(value)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let condition = translate_expr(cond);
            let then = translate_expr(then);
            let else_ = else_opt.as_ref().map(translate_expr);
            dst::ExprKind::If {
                condition,
                then,
                else_,
            }
        }
        src::ExprKind::Call {
            fun,
            args,
            generic_args,
            bounds_impls,
            r#trait,
            ..
        } => {
            let head = translate_expr(fun);
            let args = args.iter().map(translate_expr).collect::<Vec<_>>();
            let generic_args = translate_generic_args(generic_args, span);

            let trait_ = /* r#trait
                .as_ref()
                .map(|(impl_expr, g_args)| (dst::ImplExpr, translate_generic_args(&g_args, span))) */
                None;
            dst::ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls: Vec::new(),
                trait_,
            }
        }
        src::ExprKind::Deref { arg } => dst::ExprKind::Deref(translate_expr(arg)),
        src::ExprKind::Binary { op, lhs, rhs } => dst::helper::simple_app(
            dst::GlobalId::bin_op(op),
            vec![translate_expr(lhs), translate_expr(rhs)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::LogicalOp { op, lhs, rhs } => dst::helper::simple_app(
            dst::GlobalId::logical_op(op),
            vec![translate_expr(lhs), translate_expr(rhs)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::Unary { op, arg } => dst::helper::simple_app(
            GlobalId::un_op(op),
            vec![translate_expr(arg)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::Cast { source } => todo!(),
        src::ExprKind::Use { source } => *(translate_expr(source).kind),
        src::ExprKind::NeverToAny { source } => dst::helper::simple_app(
            GlobalId::never_to_any(),
            vec![translate_expr(source)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::PointerCoercion { cast, source } => return translate_expr(source),
        src::ExprKind::Loop { body } => todo!()/* dst::ExprKind::Loop {
            body: translate_expr(body),
            label: None,
        } */,
        src::ExprKind::Match { scrutinee, arms } => {
            let scrutinee = translate_expr(scrutinee);
            let arms: Vec<dst::Arm> = arms
                .iter()
                .map(|arm| {
                    let pat = translate_pat(&arm.pattern);
                    let body = translate_expr(&arm.body);
                    let guard = None; // TODO
                    let meta = dst::Metadata {
                        span: (&arm.span).into(),
                        attributes: vec![],
                    };
                    dst::Arm {
                        pat,
                        body,
                        guard,
                        meta,
                    }
                })
                .collect();
            dst::ExprKind::Match { scrutinee, arms }
        }
        src::ExprKind::Let { .. } => panic!("`Let` nodes are supposed to be pre-processed"),
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
                        attributes: vec![],
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
                                kind: Box::new(dst::PatKind::Wild),
                                ty: rhs.ty.clone(),
                                meta: dst::Metadata {
                                    attributes: vec![],
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
                        attributes: vec![],
                    },
                }
            }
            return terminator;
        }
        src::ExprKind::Assign { lhs, rhs } => todo!()/* dst::ExprKind::Assign {
            lhs: translate_expr(lhs),
            value: translate_expr(rhs),
        } */,
        src::ExprKind::AssignOp { op, lhs, rhs } => todo!()/* dst::ExprKind::Assign {
            lhs: translate_expr(lhs),
            value: dst::Expr {
                kind: Box::new(dst::helper::simple_app(
                    dst::GlobalId::bin_op(op),
                    vec![translate_expr(lhs), translate_expr(rhs)],
                    ty.clone(),
                    span.clone(),
                )),
                ty: ty.clone(),
                meta: dst::Metadata {
                    span,
                    attributes: vec![],
                },
            },
        } */,
        src::ExprKind::Field { field, lhs } => todo!(),
        src::ExprKind::TupleField { field, lhs } => dst::helper::simple_app(
            dst::GlobalId::tuple_field(*field),
            vec![translate_expr(lhs)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::Index { lhs, index } => dst::helper::simple_app(
            dst::GlobalId::index(),
            vec![translate_expr(lhs), translate_expr(index)],
            ty.clone(),
            span.clone(),
        ),
        src::ExprKind::VarRef { id } => dst::ExprKind::LocalId(id.into()),
        src::ExprKind::ConstRef { id } | src::ExprKind::ConstParam { param: id, .. } => {
            dst::ExprKind::LocalId((&(*id.name)).into())
        }
        src::ExprKind::GlobalName { id, constructor } => dst::ExprKind::GlobalId(id.clone().into()),
        src::ExprKind::UpvarRef { var_hir_id, .. } => dst::ExprKind::LocalId(var_hir_id.into()),
        src::ExprKind::Borrow { borrow_kind, arg } => dst::ExprKind::Borrow {
            mutable: false,
            inner: translate_expr(arg),
        },
        src::ExprKind::RawBorrow { mutability, arg } => todo!(),
        src::ExprKind::Break { label, value } => {
            let value = value
                .as_ref()
                .map(translate_expr)
                .unwrap_or(unit_expr(span));
            dst::ExprKind::Break {
                value,
                label: None, // TODO
            }
        }
        src::ExprKind::Continue { label } => dst::ExprKind::Continue { label: None }, // TODO
        src::ExprKind::Return { value } => {
            let value = value
                .as_ref()
                .map(translate_expr)
                .unwrap_or(unit_expr(span));
            dst::ExprKind::Return { value }
        }
        src::ExprKind::ConstBlock { did, args } => unimplemented!(),
        src::ExprKind::Repeat { value, count } => todo!(),
        src::ExprKind::Array { fields } => {
            dst::ExprKind::Array(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Tuple { fields } => {
            dst::ExprKind::Tuple(fields.iter().map(translate_expr).collect())
        }
        src::ExprKind::Adt(adt_expr) => {
            let constructor = GlobalId::from(adt_expr.info.variant.clone());
            let is_struct = matches!(adt_expr.info.kind, src::VariantKind::Struct { .. });
            let is_record = match adt_expr.info.kind {
                src::VariantKind::Struct { named } | src::VariantKind::Enum { named, .. } => named,
                _ => unimplemented!(),
            };
            let base = match adt_expr.base {
                src::AdtExprBase::None => None,
                src::AdtExprBase::Base(ref base) => Some(translate_expr(&base.base)),
                src::AdtExprBase::DefaultFields(_) => unimplemented!(),
            };
            let fields = adt_expr
                .fields
                .iter()
                .map(|f| {
                    let field = GlobalId::from(f.field.clone());
                    let value = translate_expr(&f.value);
                    (field, value)
                })
                .collect::<Vec<_>>();
            dst::ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            }
        }
        src::ExprKind::PlaceTypeAscription { source, user_ty } => panic!("place type ascription"),
        src::ExprKind::ValueTypeAscription { source, user_ty } => *translate_expr(source).kind,
        src::ExprKind::Closure {
            params,
            body,
            upvars,
            ..
        } => {
            let params = params
                .iter()
                .filter_map(|param| param.pat.as_ref().map(translate_pat))
                .collect::<Vec<_>>();
            let captures = upvars.iter().map(translate_expr).collect::<Vec<_>>();
            dst::ExprKind::Closure {
                params,
                body: translate_expr(body),
                captures,
            }
        }
        src::ExprKind::Literal { lit, neg } => dst::ExprKind::Literal(match lit.node {
            src::LitKind::Bool(bool) => dst::Literal::Bool(bool),
            src::LitKind::Int(value, _) => translate_int_literal(&ty, value, *neg),
            _ => unimplemented!(),
        }),
        src::ExprKind::ZstLiteral { user_ty } => panic!("zst literal expression"),
        src::ExprKind::NamedConst {
            def_id,
            args,
            user_ty,
            r#impl,
        } => {
            let f = GlobalId::from(def_id.clone());
            let args = translate_generic_args(args, span);
            let const_args = args
                .into_iter()
                .filter_map(|gv| {
                    if let GenericValue::Expr(e) = gv {
                        Some(e)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if const_args.is_empty() && r#impl.is_none() {
                dst::ExprKind::GlobalId(f)
            } else {
                todo!()
            }
        }
        src::ExprKind::StaticRef { def_id, .. } => dst::ExprKind::GlobalId(def_id.clone().into()),
        src::ExprKind::Yield { value } => unimplemented!(),
        src::ExprKind::Todo(_) => panic!("todo expression"),
    };
    dst::Expr {
        kind: Box::new(kind),
        ty,
        meta: dst::Metadata {
            span,
            attributes: vec![],
        },
    }
}
fn translate_attributes(_attributes: &[src::Attribute]) -> Vec<dst::Attribute> {
    vec![]
}

fn translate_generic_param(generic_param: &src::GenericParam<Body>) -> dst::GenericParam {
    let ident: dst::LocalId = match &generic_param.name {
        src::ParamName::Plain(id) => id.into(),
        _ => unimplemented!(), // TODO
    };
    let span = (&generic_param.span).into();
    let meta = dst::Metadata {
        span,
        attributes: vec![],
    };
    let kind: GenericParamKind = match &generic_param.kind {
        src::GenericParamKind::Lifetime { .. } => dst::GenericParamKind::Lifetime,
        src::GenericParamKind::Const { ty, .. } => dst::GenericParamKind::Const {
            ty: translate_ty(ty, span),
        },
        src::GenericParamKind::Type { .. } => dst::GenericParamKind::Type,
    };
    dst::GenericParam { ident, meta, kind }
}

fn translate_clause(clause: &src::Clause) -> Option<dst::GenericConstraint> {
    None
} //TODO

fn translate_generics(generics: &src::Generics<src::Expr>) -> dst::Generics {
    dst::Generics {
        params: generics
            .params
            .iter()
            .map(translate_generic_param)
            .collect::<Vec<_>>(),
        constraints: generics
            .bounds
            .iter()
            .filter_map(translate_clause)
            .collect::<Vec<_>>(), // TODO dedup
    }
}

pub fn translate_item_kind(
    item_kind: &src::ItemKind<Body>,
    name: dst::GlobalId,
    span: dst::Span,
) -> dst::ItemKind {
    match item_kind {
        src::ItemKind::Fn { def, generics, .. } => {
            let params = def
                .params
                .iter()
                .map(|param| translate_param(param, span))
                .collect::<Result<_, _>>();
            let params = match params {
                Ok(params) => params,
                Err(diag_info) => {
                    return dst::ItemKind::Error(Diagnostic::new(
                        dst::Fragment::Unknown(format!("Rust THIR: param in function <{name:?}>")),
                        diag_info,
                    ))
                }
            };
            let generics = translate_generics(generics);
            dst::ItemKind::Fn {
                name,
                generics,
                body: translate_expr(&def.body),
                params,
                safety: dst::SafetyKind::Safe,
            }
        }
        _ => dst::ItemKind::Error(Diagnostic::new(
            dst::Fragment::Unknown(format!("Rust THIR: item: {item_kind:?}")),
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
            attributes: translate_attributes(&item.attributes.attributes[..]),
        },
    }
}
