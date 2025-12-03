use crate::ast;
use crate::ast::identifiers::global_id::TupleId;
use crate::symbol::Symbol;
use hax_frontend_exporter as frontend;

trait SpannedImport<Out> {
    fn spanned_import(&self, span: ast::span::Span) -> Out;
}

pub trait Import<Out> {
    fn import(&self) -> Out;
}

impl<T: Import<Out>, Out> Import<Vec<Out>> for Vec<T> {
    fn import(&self) -> Vec<Out> {
        self.into_iter().map(Import::import).collect()
    }
}

impl<T: SpannedImport<Out>, Out> SpannedImport<Vec<Out>> for Vec<T> {
    fn spanned_import(&self, span: ast::span::Span) -> Vec<Out> {
        self.into_iter()
            .map(|value| value.spanned_import(span.clone()))
            .collect()
    }
}

impl Import<ast::GlobalId> for frontend::DefId {
    fn import(&self) -> ast::GlobalId {
        ast::GlobalId::from_frontend(self.clone())
    }
}

impl Import<ast::span::Span> for frontend::Span {
    fn import(&self) -> ast::span::Span {
        self.into()
    }
}

impl Import<Option<ast::Attribute>> for frontend::Attribute {
    fn import(&self) -> Option<ast::Attribute> {
        match self {
            frontend::Attribute::Parsed(frontend::AttributeKind::DocComment {
                kind,
                span,
                comment,
                ..
            }) => {
                let kind = match kind {
                    frontend::CommentKind::Block => ast::DocCommentKind::Block,
                    frontend::CommentKind::Line => ast::DocCommentKind::Line,
                };
                Some(ast::Attribute {
                    kind: ast::AttributeKind::DocComment {
                        kind,
                        body: comment.clone(),
                    },
                    span: span.import(),
                })
            }
            frontend::Attribute::Parsed(frontend::AttributeKind::AutomaticallyDerived(span)) => {
                let kind = ast::AttributeKind::Tool {
                    path: "automatically_derived".to_owned(),
                    tokens: String::new(),
                };
                Some(ast::Attribute {
                    kind,
                    span: span.import(),
                })
            }
            frontend::Attribute::Unparsed(frontend::AttrItem {
                path,
                args:
                    frontend::AttrArgs::Eq {
                        expr: frontend::MetaItemLit { symbol, .. },
                        ..
                    },
                span,
            }) if path == "doc" => {
                let kind = ast::AttributeKind::DocComment {
                    kind: ast::DocCommentKind::Line,
                    body: symbol.clone(),
                };
                Some(ast::Attribute {
                    kind,
                    span: span.import(),
                })
            }
            frontend::Attribute::Unparsed(frontend::AttrItem { path, args, span }) => {
                let tokens =
                    if let frontend::AttrArgs::Delimited(frontend::DelimArgs { tokens, .. }) = args
                    {
                        tokens.clone()
                    } else {
                        String::new()
                    };
                Some(ast::Attribute {
                    kind: ast::AttributeKind::Tool {
                        path: path.clone(),
                        tokens,
                    },
                    span: span.import(),
                })
            }
            _ => None,
        }
    }
}

impl Import<ast::Attributes> for Vec<frontend::Attribute> {
    fn import(&self) -> ast::Attributes {
        self.iter()
            .filter_map(frontend::Attribute::import)
            .collect()
    }
}

impl Import<ast::GenericParam> for frontend::GenericParamDef {
    fn import(&self) -> ast::GenericParam {
        // TODO #1763 missing span and attributes
        let span = ast::span::Span::dummy();
        let frontend::GenericParamDef { name, kind, .. } = self;
        let kind = match kind {
            frontend::GenericParamDefKind::Lifetime => ast::GenericParamKind::Lifetime,
            frontend::GenericParamDefKind::Type { .. } => ast::GenericParamKind::Type,
            frontend::GenericParamDefKind::Const { ty, .. } => ast::GenericParamKind::Const {
                ty: ty.spanned_import(span.clone()),
            },
        };
        ast::GenericParam {
            ident: ast::LocalId(Symbol::new(name.clone())),
            meta: ast::Metadata {
                span,
                attributes: Vec::new(),
            },
            kind,
        }
    }
}

impl SpannedImport<ast::GenericValue> for frontend::GenericArg {
    fn spanned_import(&self, span: ast::span::Span) -> ast::GenericValue {
        match self {
            frontend::GenericArg::Lifetime(_) => ast::GenericValue::Lifetime,
            frontend::GenericArg::Type(ty) => ast::GenericValue::Ty(ty.spanned_import(span)),
            frontend::GenericArg::Const(decorated) => {
                ast::GenericValue::Expr(frontend::Expr::from(decorated.clone()).import())
            }
        }
    }
}

impl Import<Vec<ast::GenericParam>> for frontend::TyGenerics {
    fn import(&self) -> Vec<ast::GenericParam> {
        self.params
            .iter()
            .map(frontend::GenericParamDef::import)
            .collect()
    }
}

impl SpannedImport<Option<ast::GenericConstraint>> for frontend::Clause {
    fn spanned_import(&self, span: ast::span::Span) -> Option<ast::GenericConstraint> {
        match &self.kind.value {
            frontend::ClauseKind::Trait(trait_predicate) => {
                let args = trait_predicate.trait_ref.generic_args.spanned_import(span);
                let trait_ = trait_predicate.trait_ref.def_id.import();
                let goal = ast::TraitGoal { trait_, args };

                Some(ast::GenericConstraint::Type(ast::ImplIdent {
                    goal,
                    name: impl_expr_name(self.id.0),
                }))
            }
            frontend::ClauseKind::Projection(frontend::ProjectionPredicate {
                impl_expr,
                assoc_item,
                ty,
            }) => {
                let impl_ = impl_expr.spanned_import(span.clone());
                let assoc_item = assoc_item.def_id.import();
                let ty = ty.spanned_import(span);
                Some(ast::GenericConstraint::Projection(
                    ast::ProjectionPredicate {
                        impl_,
                        assoc_item,
                        ty,
                    },
                ))
            }
            _ => None,
        }
    }
}

impl Import<Vec<ast::GenericConstraint>> for frontend::GenericPredicates {
    fn import(&self) -> Vec<ast::GenericConstraint> {
        self.predicates
            .iter()
            .filter_map(|(clause, span)| clause.spanned_import(span.import()))
            .collect()
    }
}

impl Import<ast::Generics> for frontend::ParamEnv {
    fn import(&self) -> ast::Generics {
        ast::Generics {
            params: self.generics.import(),
            constraints: self.predicates.import(),
        }
    }
}

impl Import<ast::SafetyKind> for frontend::Safety {
    fn import(&self) -> ast::SafetyKind {
        match self {
            frontend::Safety::Unsafe => ast::SafetyKind::Unsafe,
            frontend::Safety::Safe => ast::SafetyKind::Safe,
        }
    }
}

fn unit_ty() -> ast::TyKind {
    ast::TyKind::App {
        head: ast::GlobalId::unit_ty(),
        args: Vec::new(),
    }
}

fn import_fn_sig(fn_sig: &frontend::TyFnSig, span: ast::span::Span) -> ast::TyKind {
    let inputs = if fn_sig.inputs.is_empty() {
        vec![ast::Ty(Box::new(unit_ty()))]
    } else {
        fn_sig
            .inputs
            .iter()
            .map(|t| frontend::Ty::spanned_import(t, span.clone()))
            .collect()
    };
    ast::TyKind::Arrow {
        inputs,
        output: fn_sig.output.spanned_import(span),
    }
}

impl SpannedImport<ast::Ty> for frontend::Ty {
    fn spanned_import(&self, span: ast::span::Span) -> ast::Ty {
        let kind = match self.kind() {
            frontend::TyKind::Bool => ast::TyKind::Primitive(ast::PrimitiveTy::Bool),
            frontend::TyKind::Char => ast::TyKind::Primitive(ast::PrimitiveTy::Char),
            frontend::TyKind::Int(int_ty) => {
                ast::TyKind::Primitive(ast::PrimitiveTy::Int(int_ty.into()))
            }
            frontend::TyKind::Uint(uint_ty) => {
                ast::TyKind::Primitive(ast::PrimitiveTy::Int(uint_ty.into()))
            }
            frontend::TyKind::Float(float_ty) => {
                ast::TyKind::Primitive(ast::PrimitiveTy::Float(float_ty.into()))
            }
            frontend::TyKind::FnDef { fn_sig, .. } | frontend::TyKind::Arrow(fn_sig) => {
                import_fn_sig(&fn_sig.as_ref().value, span.clone())
            }
            frontend::TyKind::Closure(frontend::ClosureArgs { fn_sig, .. }) => {
                import_fn_sig(&fn_sig.value, span.clone())
            }
            frontend::TyKind::Adt(item_ref) => {
                let head = item_ref.def_id.import();
                let args = item_ref.generic_args.spanned_import(span.clone());
                ast::TyKind::App { head, args }
            }
            frontend::TyKind::Foreign(..) => unimplemented!(), // TODO proper hax error for issue 928
            frontend::TyKind::Str => ast::TyKind::Primitive(ast::PrimitiveTy::Str),
            frontend::TyKind::Array(item_ref) => {
                let [
                    frontend::GenericArg::Type(ty),
                    frontend::GenericArg::Const(length),
                ] = &item_ref.generic_args[..]
                else {
                    panic!(
                        "Wrong generics for array: expected a type and a constant. See synthetic_items in hax frontend."
                    )
                };
                ast::TyKind::Array {
                    ty: ty.spanned_import(span.clone()),
                    length: Box::new(length.import()),
                }
            }
            frontend::TyKind::Slice(ty) => {
                let [frontend::GenericArg::Type(ty)] = &ty.generic_args[..] else {
                    panic!(
                        "Wrong generics for slice: expected a type. See synthetic_items in hax frontend."
                    )
                };
                ast::TyKind::Slice(ty.spanned_import(span.clone()))
            }
            frontend::TyKind::RawPtr(..) => ast::TyKind::RawPointer,
            frontend::TyKind::Ref(_region, ty, mutable) => ast::TyKind::Ref {
                inner: ty.as_ref().spanned_import(span.clone()),
                mutable: *mutable,
                region: ast::Region,
            },
            frontend::TyKind::Dynamic(_, generic_predicates, _region) => {
                let goals = generic_predicates
                    .predicates
                    .iter()
                    .map(|(clause, _span)| match &clause.kind.value {
                        frontend::ClauseKind::Trait(frontend::TraitPredicate {
                            trait_ref, ..
                        }) => ast::DynTraitGoal {
                            trait_: trait_ref.def_id.import(),
                            non_self_args: trait_ref.generic_args.spanned_import(span.clone())[1..]
                                .to_vec(),
                        },
                        _ => panic!("type Dyn with non trait predicate"),
                    })
                    .collect();
                ast::TyKind::Dyn(goals)
            }
            frontend::TyKind::Coroutine(_) => unimplemented!("coroutines are not supported by hax"), // TODO link to hax issue 924
            frontend::TyKind::Never => ast::TyKind::App {
                head: crate::names::rust_primitives::hax::Never,
                args: Vec::new(),
            },
            frontend::TyKind::Tuple(item_ref) => {
                let args = item_ref.generic_args.spanned_import(span.clone());
                ast::TyKind::App {
                    head: TupleId::Type { length: args.len() }.into(),
                    args,
                }
            }
            frontend::TyKind::Alias(frontend::Alias {
                kind: frontend::AliasKind::Projection { impl_expr, .. },
                def_id,
                ..
            }) => ast::TyKind::AssociatedType {
                impl_: impl_expr.spanned_import(span.clone()),
                item: def_id.import(),
            },
            frontend::TyKind::Alias(frontend::Alias {
                kind: frontend::AliasKind::Opaque { .. },
                def_id,
                ..
            }) => ast::TyKind::Opaque(def_id.import()),
            frontend::TyKind::Alias(frontend::Alias {
                kind: frontend::AliasKind::Inherent,
                ..
            }) => panic!("Ty::Alias with AliasTyKind::Inherent"),
            frontend::TyKind::Alias(frontend::Alias {
                kind: frontend::AliasKind::Free,
                ..
            }) => panic!("Ty::Alias with AliasTyKind::Free"),
            frontend::TyKind::Param(frontend::ParamTy { name, .. }) => {
                ast::TyKind::Param(ast::LocalId(Symbol::new(name.clone())))
            }
            frontend::TyKind::Bound(..) => panic!("type Bound: should be gone after typechecking"),
            frontend::TyKind::Placeholder(..) => {
                panic!("type Placeholder: should be gone after typechecking")
            }
            frontend::TyKind::Infer(..) => panic!("type Infer: should be gone after typechecking"),
            frontend::TyKind::Error => {
                panic!("got type `Error`: Rust compilation probably failed.")
            }
            frontend::TyKind::Todo(_) => panic!("type Todo"),
        };
        ast::Ty(Box::new(kind))
    }
}

impl SpannedImport<ast::literals::Literal> for frontend::ConstantLiteral {
    fn spanned_import(&self, span: ast::span::Span) -> ast::literals::Literal {
        match self {
            frontend::ConstantLiteral::Bool(b) => ast::literals::Literal::Bool(*b),
            frontend::ConstantLiteral::Char(c) => ast::literals::Literal::Char(*c),
            frontend::ConstantLiteral::Float(f, float_ty) => match f.strip_prefix("-") {
                Some(f) => ast::literals::Literal::Float {
                    value: Symbol::new(f),
                    negative: true,
                    kind: float_ty.into(),
                },
                None => ast::literals::Literal::Float {
                    value: Symbol::new(f),
                    negative: false,
                    kind: float_ty.into(),
                },
            },
            frontend::ConstantLiteral::Int(frontend::ConstantInt::Int(v, ty)) => {
                ast::literals::Literal::Int {
                    value: Symbol::new(v.abs().to_string()),
                    negative: *v < 0,
                    kind: ty.into(),
                }
            }
            frontend::ConstantLiteral::Int(frontend::ConstantInt::Uint(v, ty)) => {
                ast::literals::Literal::Int {
                    value: Symbol::new(v.to_string()),
                    negative: false,
                    kind: ty.into(),
                }
            }
            frontend::ConstantLiteral::PtrNoProvenance(_) => {
                panic!("constant literal: PtrNoProvenance")
            } // TODO proper error
            frontend::ConstantLiteral::Str(s) => ast::literals::Literal::String(Symbol::new(s)),
            frontend::ConstantLiteral::ByteStr(items) => {
                let s = String::from_utf8_lossy(items).to_string();
                ast::literals::Literal::String(Symbol::new(&s))
            } // TODO deal with this by returning an "extendedliteral", or return an expr_kind here
              // which can be an array of literals (deal with it by making an array expr)
        }
    }
}

impl Import<ast::Expr> for frontend::ConstantExpr {
    fn import(&self) -> ast::Expr {
        let Self {
            ty,
            span,
            contents,
            attributes,
            ..
        } = self;
        let span = span.import();
        let attributes = attributes.import();
        let kind = Box::new(ast::ExprKind::Construct {
            constructor: ast::GlobalId::unit_constructor(),
            is_record: false,
            is_struct: true,
            fields: Vec::new(),
            base: None,
        });
        ast::Expr {
            kind,
            ty: ty.spanned_import(span.clone()),
            meta: ast::Metadata { span, attributes },
        }
    }
}

impl Import<ast::Expr> for frontend::Expr {
    fn import(&self) -> ast::Expr {
        let Self {
            ty,
            span,
            contents,
            attributes,
            ..
        } = self;
        let span = span.import();
        macro_rules! todo {
            () => {
                ast::ExprKind::Construct {
                    constructor: ast::GlobalId::unit_constructor(),
                    is_record: false,
                    is_struct: true,
                    fields: Vec::new(),
                    base: None,
                }
            };
        }
        let binop_id = |op: &frontend::BinOp| match op {
            frontend::BinOp::Add
            | frontend::BinOp::AddWithOverflow
            | frontend::BinOp::AddUnchecked => crate::names::rust_primitives::hax::machine_int::add,
            frontend::BinOp::Sub
            | frontend::BinOp::SubWithOverflow
            | frontend::BinOp::SubUnchecked => crate::names::rust_primitives::hax::machine_int::sub,
            frontend::BinOp::Mul
            | frontend::BinOp::MulWithOverflow
            | frontend::BinOp::MulUnchecked => crate::names::rust_primitives::hax::machine_int::mul,
            frontend::BinOp::Div => crate::names::rust_primitives::hax::machine_int::div,
            frontend::BinOp::Rem => crate::names::rust_primitives::hax::machine_int::rem,
            frontend::BinOp::BitXor => {
                crate::names::rust_primitives::hax::machine_int::bitxor
            }
            frontend::BinOp::BitAnd => {
                crate::names::rust_primitives::hax::machine_int::bitand
            }
            frontend::BinOp::BitOr => crate::names::rust_primitives::hax::machine_int::bitor,
            frontend::BinOp::Shl | frontend::BinOp::ShlUnchecked => {
                crate::names::rust_primitives::hax::machine_int::shl
            }
            frontend::BinOp::Shr | frontend::BinOp::ShrUnchecked => {
                crate::names::rust_primitives::hax::machine_int::shr
            }
            frontend::BinOp::Lt => crate::names::rust_primitives::hax::machine_int::lt,
            frontend::BinOp::Le => crate::names::rust_primitives::hax::machine_int::le,
            frontend::BinOp::Ne => crate::names::rust_primitives::hax::machine_int::ne,
            frontend::BinOp::Ge => crate::names::rust_primitives::hax::machine_int::ge,
            frontend::BinOp::Gt => crate::names::rust_primitives::hax::machine_int::gt,
            frontend::BinOp::Eq => crate::names::rust_primitives::hax::machine_int::eq,
            frontend::BinOp::Offset => crate::names::rust_primitives::hax::machine_int::add,
            frontend::BinOp::Cmp => crate::names::rust_primitives::hax::machine_int::eq,
        };
        let assign_binop = |op: &frontend::AssignOp| match op {
            frontend::AssignOp::AddAssign => frontend::BinOp::Add,
            frontend::AssignOp::SubAssign => frontend::BinOp::Sub,
            frontend::AssignOp::MulAssign => frontend::BinOp::Mul,
            frontend::AssignOp::DivAssign => frontend::BinOp::Div,
            frontend::AssignOp::RemAssign => frontend::BinOp::Rem,
            frontend::AssignOp::BitXorAssign => frontend::BinOp::BitXor,
            frontend::AssignOp::BitAndAssign => frontend::BinOp::BitAnd,
            frontend::AssignOp::BitOrAssign => frontend::BinOp::BitOr,
            frontend::AssignOp::ShlAssign => frontend::BinOp::Shl,
            frontend::AssignOp::ShrAssign => frontend::BinOp::Shr,
        };
        let unit_ty = || ast::Ty(Box::new(ast::TyKind::App {
            head: TupleId::Type { length: 0 }.into(),
            args: Vec::new(),
        }));
        let unit_expr = |span: ast::span::Span| ast::Expr {
            kind: Box::new(ast::ExprKind::Construct {
                constructor: ast::GlobalId::unit_constructor(),
                is_record: false,
                is_struct: true,
                fields: Vec::new(),
                base: None,
            }),
            ty: unit_ty(),
            meta: ast::Metadata {
                span,
                attributes: Vec::new(),
            },
        };
        let mk_app = |id: ast::GlobalId,
                      inputs: Vec<ast::Ty>,
                      output: ast::Ty,
                      args: Vec<ast::Expr>,
                      span: ast::span::Span| {
            let head = ast::Expr {
                kind: Box::new(ast::ExprKind::GlobalId(id)),
                ty: ast::Ty(Box::new(ast::TyKind::Arrow {
                    inputs,
                    output: output.clone(),
                })),
                meta: ast::Metadata {
                    span: span.clone(),
                    attributes: Vec::new(),
                },
            };
            ast::ExprKind::App {
                head,
                args,
                generic_args: Vec::new(),
                bounds_impls: Vec::new(),
                trait_: None,
            }
        };
        let kind = match contents.as_ref() {
            frontend::ExprKind::Box { value } => {
                let value = value.import();
                let ty = ty.spanned_import(span.clone());
                let id = crate::names::rust_primitives::hax::box_new;
                mk_app(id, vec![value.ty.clone()], ty, vec![value], span.clone())
            }
            frontend::ExprKind::If {
                if_then_scope,
                cond,
                then,
                else_opt,
            } => {
                if let frontend::ExprKind::Let { expr, pat } = cond.contents.as_ref() {
                    let scrutinee = expr.import();
                    let pat = pat.import();
                    let then_expr = then.import();
                    let else_expr = else_opt
                        .as_ref()
                        .map(Import::import)
                        .unwrap_or_else(|| unit_expr(span.clone()));
                    let arm_then = ast::Arm {
                        pat,
                        body: then_expr,
                        guard: None,
                        meta: ast::Metadata {
                            span: span.clone(),
                            attributes: Vec::new(),
                        },
                    };
                    let wildcard_pat = ast::Pat {
                        kind: Box::new(ast::PatKind::Wild),
                        ty: arm_then.pat.ty.clone(),
                        meta: arm_then.pat.meta.clone(),
                    };
                    let arm_else = ast::Arm {
                        pat: wildcard_pat,
                        body: else_expr,
                        guard: None,
                        meta: ast::Metadata {
                            span: span.clone(),
                            attributes: Vec::new(),
                        },
                    };
                    ast::ExprKind::Match {
                        scrutinee,
                        arms: vec![arm_then, arm_else],
                    }
                } else {
                    ast::ExprKind::If {
                        condition: cond.import(),
                        then: then.import(),
                        else_: else_opt.as_ref().map(Import::import),
                    }
                }
            }
            frontend::ExprKind::Call {
                ty,
                fun,
                args,
                from_hir_call,
                fn_span,
            } => {
                let mut args = args.import();
                if args.is_empty() {
                    args.push(unit_expr(span.clone()));
                }
                let head = fun.import();
                ast::ExprKind::App {
                    head,
                    args,
                    generic_args: Vec::new(),
                    bounds_impls: Vec::new(),
                    trait_: None,
                }
            }
            frontend::ExprKind::Deref { arg } => {
                ast::ExprKind::Deref(arg.import())
            }
            frontend::ExprKind::Binary { op, lhs, rhs } => {
                let lhs_ty = lhs.ty.spanned_import(span.clone());
                let rhs_ty = rhs.ty.spanned_import(span.clone());
                let result_ty = ty.spanned_import(span.clone());
                let id = binop_id(op);
                mk_app(
                    id,
                    vec![lhs_ty.clone(), rhs_ty.clone()],
                    result_ty,
                    vec![lhs.import(), rhs.import()],
                    span.clone(),
                )
            }
            frontend::ExprKind::LogicalOp { op, lhs, rhs } => {
                let lhs_ty = lhs.ty.spanned_import(span.clone());
                let rhs_ty = rhs.ty.spanned_import(span.clone());
                let result_ty = ty.spanned_import(span.clone());
                let id = match op {
                    frontend::LogicalOp::And => {
                        crate::names::rust_primitives::hax::logical_op_and
                    }
                    frontend::LogicalOp::Or => crate::names::rust_primitives::hax::logical_op_or,
                };
                mk_app(
                    id,
                    vec![lhs_ty.clone(), rhs_ty.clone()],
                    result_ty,
                    vec![lhs.import(), rhs.import()],
                    span.clone(),
                )
            }
            frontend::ExprKind::Unary { op, arg } => {
                let arg_ty = arg.ty.spanned_import(span.clone());
                let result_ty = ty.spanned_import(span.clone());
                let id = match op {
                    frontend::UnOp::Not => {
                        crate::names::core::ops::bit::Not::not
                    }
                    frontend::UnOp::Neg => {
                        crate::names::core::ops::arith::Neg::neg
                    }
                    frontend::UnOp::PtrMetadata => {
                        crate::names::rust_primitives::hax::cast_op
                    }
                };
                mk_app(id, vec![arg_ty.clone()], result_ty, vec![arg.import()], span.clone())
            }
            frontend::ExprKind::Cast { source } => {
                mk_app(
                    crate::names::rust_primitives::hax::cast_op,
                    vec![source.ty.spanned_import(span.clone())],
                    ty.spanned_import(span.clone()),
                    vec![source.import()],
                    span.clone(),
                )
            }
            frontend::ExprKind::Use { source } => return source.import(),
            frontend::ExprKind::NeverToAny { source } => mk_app(
                crate::names::rust_primitives::hax::never_to_any,
                vec![source.ty.spanned_import(span.clone())],
                ty.spanned_import(span.clone()),
                vec![source.import()],
                span.clone(),
            ),
            frontend::ExprKind::PointerCoercion { cast: _, source } => {
                mk_app(
                    crate::names::rust_primitives::hax::cast_op,
                    vec![source.ty.spanned_import(span.clone())],
                    ty.spanned_import(span.clone()),
                    vec![source.import()],
                    span.clone(),
                )
            }
            frontend::ExprKind::Loop { body } => ast::ExprKind::Loop {
                body: body.import(),
                kind: Box::new(ast::LoopKind::UnconditionalLoop),
                state: None,
                control_flow: None,
                label: None,
            },
            frontend::ExprKind::Match { scrutinee, arms } => ast::ExprKind::Match {
                scrutinee: scrutinee.import(),
                arms: arms
                    .iter()
                    .map(|arm| {
                        ast::Arm {
                            pat: arm.pattern.import(),
                            body: arm.body.import(),
                            guard: arm.guard.as_ref().map(|g| ast::Guard {
                                kind: match g.contents.as_ref() {
                                    frontend::ExprKind::Let { expr, pat } => {
                                        ast::GuardKind::IfLet {
                                            lhs: pat.import(),
                                            rhs: expr.import(),
                                        }
                                    }
                                    _ => ast::GuardKind::IfLet {
                                        lhs: ast::Pat {
                                            kind: Box::new(ast::PatKind::Constant {
                                                lit: ast::literals::Literal::Bool(true),
                                            }),
                                            ty: ast::Ty(Box::new(ast::TyKind::Primitive(
                                                ast::PrimitiveTy::Bool,
                                            ))),
                                            meta: ast::Metadata {
                                                span: span.clone(),
                                                attributes: Vec::new(),
                                            },
                                        },
                                        rhs: g.import(),
                                    },
                                },
                                meta: ast::Metadata {
                                    span: g.span.import(),
                                    attributes: g.attributes.import(),
                                },
                            }),
                            meta: ast::Metadata {
                                span: arm.span.import(),
                                attributes: Vec::new(),
                            },
                        }
                    })
                    .collect(),
            },
            frontend::ExprKind::Let { expr, pat } => panic!("Let nodes are preprocessed"),
            frontend::ExprKind::Block { block } => {
                if let Some(expr) = block.expr.as_ref() {
                    return expr.import();
                }
                let kind = ast::ExprKind::Construct {
                    constructor: ast::GlobalId::unit_constructor(),
                    is_record: false,
                    is_struct: true,
                    fields: Vec::new(),
                    base: None,
                };
                return ast::Expr {
                    kind: Box::new(kind),
                    ty: ty.spanned_import(span.clone()),
                    meta: ast::Metadata {
                        span: block.span.import(),
                        attributes: attributes.import(),
                    },
                };
            }
            frontend::ExprKind::Assign { lhs, rhs } => ast::ExprKind::Assign {
                lhs: ast::Lhs::ArbitraryExpr(Box::new(lhs.import())),
                value: rhs.import(),
            },
            frontend::ExprKind::AssignOp { op, lhs, rhs } => {
                let bin_op = assign_binop(op);
                let bin = mk_app(
                    binop_id(&bin_op),
                    vec![
                        lhs.ty.spanned_import(span.clone()),
                        rhs.ty.spanned_import(span.clone()),
                    ],
                    ty.spanned_import(span.clone()),
                    vec![lhs.import(), rhs.import()],
                    span.clone(),
                );
                let op_expr = ast::Expr {
                    kind: Box::new(bin),
                    ty: ty.spanned_import(span.clone()),
                    meta: ast::Metadata {
                        span: span.clone(),
                        attributes: Vec::new(),
                    },
                };
                ast::ExprKind::Assign {
                    lhs: ast::Lhs::ArbitraryExpr(Box::new(lhs.import())),
                    value: op_expr,
                }
            }
            frontend::ExprKind::Field { field, lhs } => {
                let lhs_ty = lhs.ty.spanned_import(span.clone());
                let result_ty = ty.spanned_import(span.clone());
                let projector = ast::Expr {
                    kind: Box::new(ast::ExprKind::GlobalId(field.import())),
                    ty: ast::Ty(Box::new(ast::TyKind::Arrow {
                        inputs: vec![lhs_ty.clone()],
                        output: result_ty.clone(),
                    })),
                    meta: ast::Metadata {
                        span: span.clone(),
                        attributes: Vec::new(),
                    },
                };
                ast::ExprKind::App {
                    head: projector,
                    args: vec![lhs.import()],
                    generic_args: Vec::new(),
                    bounds_impls: Vec::new(),
                    trait_: None,
                }
            }
            frontend::ExprKind::TupleField { field, lhs } => {
                let lhs_ty = lhs.ty.spanned_import(span.clone());
                let length = match lhs.ty.kind() {
                    frontend::TyKind::Tuple(item_ref) => item_ref.generic_args.len(),
                    _ => panic!("TupleField on non-tuple type"),
                };
                let projector: ast::GlobalId =
                    TupleId::Field { length, field: *field }.into();
                let result_ty = ty.spanned_import(span.clone());
                let head = ast::Expr {
                    kind: Box::new(ast::ExprKind::GlobalId(projector)),
                    ty: ast::Ty(Box::new(ast::TyKind::Arrow {
                        inputs: vec![lhs_ty.clone()],
                        output: result_ty.clone(),
                    })),
                    meta: ast::Metadata {
                        span: span.clone(),
                        attributes: Vec::new(),
                    },
                };
                ast::ExprKind::App {
                    head,
                    args: vec![lhs.import()],
                    generic_args: Vec::new(),
                    bounds_impls: Vec::new(),
                    trait_: None,
                }
            }
            frontend::ExprKind::Index { lhs, index } => {
                let lhs_ty = lhs.ty.spanned_import(span.clone());
                let index_ty = index.ty.spanned_import(span.clone());
                let result_ty = ty.spanned_import(span.clone());
                let id = crate::names::core::ops::index::Index::index;
                mk_app(
                    id,
                    vec![lhs_ty, index_ty],
                    result_ty,
                    vec![lhs.import(), index.import()],
                    span.clone(),
                )
            }
            frontend::ExprKind::VarRef { id } => {
                ast::ExprKind::LocalId(ast::LocalId::from(id))
            }
            frontend::ExprKind::ConstRef { id } => ast::ExprKind::LocalId(
                ast::LocalId(Symbol::new(id.name.clone())),
            ),
            frontend::ExprKind::GlobalName { item, constructor: _ } => {
                let ident = item.contents().def_id.import();
                ast::ExprKind::GlobalId(ident)
            }
            frontend::ExprKind::UpvarRef {
                closure_def_id,
                var_hir_id,
            } => ast::ExprKind::LocalId(ast::LocalId::from(var_hir_id)),
            frontend::ExprKind::Borrow { borrow_kind, arg } => {
                let inner = arg.import();
                let mutable = matches!(borrow_kind, frontend::BorrowKind::Mut { .. });
                ast::ExprKind::Borrow { mutable, inner }
            }
            frontend::ExprKind::RawBorrow { mutability, arg } => {
                ast::ExprKind::AddressOf {
                    mutable: *mutability,
                    inner: arg.import(),
                }
            }
            frontend::ExprKind::Break { label: _, value } => {
                let value = value
                    .as_ref()
                    .map(Import::import)
                    .unwrap_or_else(|| unit_expr(span.clone()));
                ast::ExprKind::Break { value, label: None }
            }
            frontend::ExprKind::Continue { label: _ } => {
                ast::ExprKind::Continue { label: None }
            }
            frontend::ExprKind::Return { value } => {
                let value = value
                    .as_ref()
                    .map(Import::import)
                    .unwrap_or_else(|| unit_expr(span.clone()));
                ast::ExprKind::Return { value }
            }
            frontend::ExprKind::ConstBlock(item_ref) => {
                ast::ExprKind::GlobalId(item_ref.contents().def_id.import())
            }
            frontend::ExprKind::Repeat { value, count: _ } => {
                ast::ExprKind::Array(vec![value.import()])
            }
            frontend::ExprKind::Array { fields } => {
                ast::ExprKind::Array(fields.import())
            }
            frontend::ExprKind::Tuple { fields } => {
                let length = fields.len();
                let constructor: ast::GlobalId =
                    TupleId::Constructor { length }.into();
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(idx, value)| {
                        let field: ast::GlobalId =
                            TupleId::Field { length, field: idx }.into();
                        (field, value.import())
                    })
                    .collect();
                ast::ExprKind::Construct {
                    constructor,
                    is_record: false,
                    is_struct: true,
                    fields,
                    base: None,
                }
            }
            frontend::ExprKind::Adt(adt_expr) => {
                let (is_struct, is_record) = match adt_expr.info.kind {
                    frontend::VariantKind::Struct { named } => (true, named),
                    frontend::VariantKind::Enum { named, .. } => (false, named),
                    frontend::VariantKind::Union => (false, false),
                };
                let constructor = adt_expr.info.variant.import();
                let base = match &adt_expr.base {
                    frontend::AdtExprBase::None => None,
                    frontend::AdtExprBase::Base(info) => Some(info.base.import()),
                    frontend::AdtExprBase::DefaultFields(_) => None,
                };
                let fields = adt_expr
                    .fields
                    .iter()
                    .map(|f| (f.field.import(), f.value.import()))
                    .collect();
                ast::ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                }
            }
            frontend::ExprKind::PlaceTypeAscription { source, user_ty }
            | frontend::ExprKind::ValueTypeAscription { source, user_ty } => {
                let ty = source.ty.spanned_import(span.clone());
                ast::ExprKind::Ascription {
                    e: source.import(),
                    ty,
                }
            }
            frontend::ExprKind::Closure {
                params,
                body,
                upvars,
                movability,
            } => {
                let params: Vec<ast::Pat> = params
                    .iter()
                    .filter_map(|p| p.pat.as_ref().map(Import::import))
                    .collect();
                ast::ExprKind::Closure {
                    params,
                    body: body.import(),
                    captures: upvars.import(),
                }
            }
            frontend::ExprKind::Literal { lit, neg } => {
                let mut literal = match &lit.node {
                    frontend::LitKind::Bool(b) => ast::literals::Literal::Bool(*b),
                    frontend::LitKind::Char(c) => ast::literals::Literal::Char(*c),
                    frontend::LitKind::Byte(b) => ast::literals::Literal::Int {
                        value: Symbol::new(b.to_string()),
                        negative: false,
                        kind: (&frontend::UintTy::U8).into(),
                    },
                    frontend::LitKind::Str(s, _) => {
                        ast::literals::Literal::String(Symbol::new(s))
                    }
                    frontend::LitKind::Int(value, kind) => {
                        use frontend::LitIntType::*;
                        let kind = match (kind, ty.kind()) {
                            (Signed(int_ty), _) => ast::literals::IntKind::from(int_ty),
                            (Unsigned(uint_ty), _) => ast::literals::IntKind::from(uint_ty),
                            (Unsuffixed, frontend::TyKind::Int(int_ty)) => {
                                ast::literals::IntKind::from(int_ty)
                            }
                            (Unsuffixed, frontend::TyKind::Uint(uint_ty)) => {
                                ast::literals::IntKind::from(uint_ty)
                            }
                            _ => panic!("Unsuffixed int literal without int/uint type"),
                        };
                        ast::literals::Literal::Int {
                            value: Symbol::new(value.to_string()),
                            negative: false,
                            kind,
                        }
                    }
                    frontend::LitKind::Float(value, float_ty) => ast::literals::Literal::Float {
                        value: Symbol::new(value),
                        negative: false,
                        kind: match (float_ty, ty.kind()) {
                            (frontend::LitFloatType::Suffixed(k), _) => {
                                ast::literals::FloatKind::from(k)
                            }
                            (frontend::LitFloatType::Unsuffixed, frontend::TyKind::Float(k)) => {
                                ast::literals::FloatKind::from(k)
                            }
                            _ => panic!("Unsuffixed float literal without float type"),
                        },
                    },
                    frontend::LitKind::ByteStr(..) | frontend::LitKind::CStr(..) => {
                        panic!("Byte string and C string literals are not supported yet")
                    }
                    frontend::LitKind::Err(_) => panic!("Error literal"),
                };
                if *neg {
                    match &mut literal {
                        ast::literals::Literal::Int { negative, .. }
                        | ast::literals::Literal::Float { negative, .. } => {
                            *negative = true;
                        }
                        _ => panic!("Unexpected negation on non-numeric literal"),
                    }
                }
                ast::ExprKind::Literal(literal)
            }
            frontend::ExprKind::ZstLiteral { user_ty: _ } => ast::ExprKind::Construct {
                constructor: ast::GlobalId::unit_constructor(),
                is_record: false,
                is_struct: true,
                fields: Vec::new(),
                base: None,
            },
            frontend::ExprKind::NamedConst { item, user_ty: _ } => {
                ast::ExprKind::GlobalId(item.contents().def_id.import())
            }
            frontend::ExprKind::ConstParam { param, def_id: _ } => ast::ExprKind::LocalId(
                ast::LocalId(Symbol::new(param.name.clone())),
            ),
            frontend::ExprKind::StaticRef {
                alloc_id,
                ty,
                def_id,
            } => ast::ExprKind::GlobalId(def_id.import()),
            frontend::ExprKind::Yield { value } => {
                ast::ExprKind::Return { value: value.import() }
            }
            frontend::ExprKind::Todo(_) => ast::ExprKind::Construct {
                constructor: ast::GlobalId::unit_constructor(),
                is_record: false,
                is_struct: true,
                fields: Vec::new(),
                base: None,
            },
        };
        ast::Expr {
            kind: Box::new(kind),
            ty: ty.spanned_import(span.clone()),
            meta: ast::Metadata {
                span,
                attributes: attributes.import(),
            },
        }
    }
}

impl Import<(ast::GlobalId, ast::Ty, Vec<ast::Attribute>)> for frontend::FieldDef {
    fn import(&self) -> (ast::GlobalId, ast::Ty, Vec<ast::Attribute>) {
        // TODO #1763 missing attributes on FieldDef
        (
            self.did.import(),
            self.ty.spanned_import(self.span.import()),
            Vec::new(),
        )
    }
}

impl Import<ast::Expr> for frontend::ThirBody {
    fn import(&self) -> ast::Expr {
        self.expr.import()
    }
}

impl Import<ast::PatKind> for frontend::PatKind {
    fn import(&self) -> ast::PatKind {
        match self {
            frontend::PatKind::Wild | frontend::PatKind::Missing => ast::PatKind::Wild,
            frontend::PatKind::AscribeUserType { subpattern, .. } => ast::PatKind::Ascription {
                pat: subpattern.import(),
                ty: ast::SpannedTy {
                    span: ast::span::Span::dummy(),
                    ty: subpattern.ty.spanned_import(ast::span::Span::dummy()),
                },
            },
            frontend::PatKind::Binding {
                mode,
                var,
                subpattern,
                ..
            } => {
                let mutable = mode.mutability;
                let mode = match mode.by_ref {
                    frontend::ByRef::Yes(_, mutability) => ast::BindingMode::ByRef(
                        if mutability { ast::BorrowKind::Mut } else { ast::BorrowKind::Shared },
                    ),
                    frontend::ByRef::No => ast::BindingMode::ByValue,
                };
                ast::PatKind::Binding {
                    mutable,
                    var: ast::LocalId::from(var),
                    mode,
                    sub_pat: subpattern.as_ref().map(Import::import),
                }
            }
            frontend::PatKind::Variant {
                info,
                subpatterns,
                ..
            } => {
                let (is_struct, is_record) = match info.kind {
                    frontend::VariantKind::Struct { named } => (true, named),
                    frontend::VariantKind::Enum { named, .. } => (false, named),
                    frontend::VariantKind::Union => (false, false),
                };
                let constructor = info.variant.import();
                let fields = subpatterns
                    .iter()
                    .map(|f| (f.field.import(), f.pattern.import()))
                    .collect();
                ast::PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                }
            }
            frontend::PatKind::Tuple { subpatterns } => {
                let length = subpatterns.len();
                let constructor: ast::GlobalId =
                    TupleId::Constructor { length }.into();
                let fields = subpatterns
                    .iter()
                    .enumerate()
                    .map(|(idx, pat)| {
                        let field: ast::GlobalId =
                            TupleId::Field { length, field: idx }.into();
                        (field, pat.import())
                    })
                    .collect();
                ast::PatKind::Construct {
                    constructor,
                    is_record: false,
                    is_struct: true,
                    fields,
                }
            }
            frontend::PatKind::Deref { subpattern }
            | frontend::PatKind::DerefPattern { subpattern } => {
                ast::PatKind::Deref {
                    sub_pat: subpattern.import(),
                }
            }
            frontend::PatKind::Constant { value } => {
                let expr = value.import();
                match *expr.kind {
                    ast::ExprKind::Literal(lit) => ast::PatKind::Constant { lit },
                    _ => ast::PatKind::Wild,
                }
            }
            frontend::PatKind::ExpandedConstant { subpattern, .. } => {
                *subpattern.import().kind
            }
            frontend::PatKind::Range(_) => ast::PatKind::Wild,
            frontend::PatKind::Slice {
                prefix,
                slice,
                suffix,
            }
            | frontend::PatKind::Array {
                prefix,
                slice,
                suffix,
            } => {
                let mut pats: Vec<frontend::Pat> = Vec::new();
                pats.extend(prefix.iter().cloned());
                if let Some(s) = slice {
                    pats.push(s.clone());
                }
                pats.extend(suffix.iter().cloned());
                ast::PatKind::Array {
                    args: pats.import(),
                }
            }
            frontend::PatKind::Or { pats } => ast::PatKind::Or {
                sub_pats: pats.import(),
            },
            frontend::PatKind::Never | frontend::PatKind::Error(_) => {
                ast::PatKind::Wild
            }
        }
    }
}
impl Import<ast::Pat> for frontend::Pat {
    fn import(&self) -> ast::Pat {
        let Self {
            ty,
            span,
            contents,
            hir_id,
            attributes,
        } = self;
        let span = span.import();
        let kind = match contents.as_ref() {
            frontend::PatKind::AscribeUserType { ascription: _, subpattern } => {
                ast::PatKind::Ascription {
                    pat: subpattern.import(),
                    ty: ast::SpannedTy {
                        span: span.clone(),
                        ty: ty.spanned_import(span.clone()),
                    },
                }
            }
            other => other.import(),
        };
        ast::Pat {
            kind: Box::new(kind),
            ty: ty.spanned_import(span.clone()),
            meta: ast::Metadata {
                span,
                attributes: attributes.import(),
            },
        }
    }
}

impl SpannedImport<ast::Param> for frontend::Param {
    fn spanned_import(&self, span: ast::span::Span) -> ast::Param {
        let frontend::Param {
            pat,
            ty,
            ty_span,
            attributes,
            ..
        } = self;
        let ty_span = ty_span.as_ref().map(Import::import);
        let ty = ty.spanned_import(ty_span.clone().unwrap_or(span.clone()));
        ast::Param {
            pat: pat
                .as_ref()
                .map(Import::import)
                .unwrap_or_else(|| ast::Pat {
                    kind: Box::new(ast::PatKind::Wild),
                    ty: ty.clone(),
                    meta: ast::Metadata {
                        span,
                        attributes: vec![],
                    },
                }),
            ty,
            ty_span: ty_span,
            attributes: attributes.import(),
        }
    }
}

impl Import<ast::Variant> for frontend::VariantDef {
    fn import(&self) -> ast::Variant {
        ast::Variant {
            name: self.def_id.import(),
            arguments: self.fields.import(),
            is_record: self.fields.raw.first().is_some_and(|fd| fd.name.is_some()),
            // TODO #1763 missing attributes on VariantDef
            attributes: Vec::new(),
        }
    }
}

impl<I, A: Import<B>, B> Import<Vec<B>> for frontend::IndexVec<I, A> {
    fn import(&self) -> Vec<B> {
        self.raw.iter().map(A::import).collect()
    }
}

fn import_trait_item(item: &frontend::FullDef<frontend::ThirBody>) -> ast::TraitItem {
    let span = item.span.import();
    let attributes = item.attributes.import();
    let meta = ast::Metadata {
        span: span.clone(),
        attributes,
    };
    let kind = match &item.kind {
        frontend::FullDefKind::AssocConst {
            body: Some(default),
            ..
        } => ast::TraitItemKind::Default {
            params: Vec::new(),
            body: default.import(),
        },
        frontend::FullDefKind::AssocConst { ty, .. } => {
            ast::TraitItemKind::Fn(ty.spanned_import(span.clone()))
        }
        frontend::FullDefKind::AssocFn {
            body: Some(default),
            ..
        } => ast::TraitItemKind::Default {
            params: Vec::new(),
            body: default.import(),
        },
        frontend::FullDefKind::AssocFn { sig, .. } => {
            let inputs = sig
                .value
                .inputs
                .iter()
                .map(|ty| ty.spanned_import(span.clone()))
                .collect();
            let output = sig.value.output.spanned_import(span);
            ast::TraitItemKind::Fn(ast::Ty(Box::new(ast::TyKind::Arrow { inputs, output })))
        }
        frontend::FullDefKind::AssocTy {
            value: Some(..), ..
        } => panic!(
            "Associate types defaults are not supported by hax yet (it is a nightly feature)"
        ), // TODO proper hax error (issue 929)
        frontend::FullDefKind::AssocTy {
            implied_predicates, ..
        } => ast::TraitItemKind::Type(
            implied_predicates
                .import()
                .into_iter()
                .filter_map(|gc| match gc {
                    ast::GenericConstraint::Type(t) => Some(t),
                    _ => None,
                })
                .collect(),
        ),
        _ => panic!("Found associated item of an unknown kind."),
    };
    let (frontend::FullDefKind::AssocConst { param_env, .. }
    | frontend::FullDefKind::AssocFn { param_env, .. }
    | frontend::FullDefKind::AssocTy { param_env, .. }) = &item.kind
    else {
        panic!("Found associated item of an unknown kind.")
    };
    ast::TraitItem {
        meta,
        kind,
        generics: param_env.import(),
        ident: item.def_id().import(),
    }
}

impl SpannedImport<ast::TraitGoal> for frontend::TraitRef {
    fn spanned_import(&self, span: ast::span::Span) -> ast::TraitGoal {
        let trait_ = self.def_id.import();
        let args = self.generic_args.spanned_import(span);
        ast::TraitGoal { trait_, args }
    }
}

fn impl_expr_name(index: u64) -> Symbol {
    Symbol::new(format!("i{}", index).to_owned())
}

fn browse_path(
    item_kind: ast::ImplExprKind,
    chunk: &frontend::ImplExprPathChunk,
    span: ast::span::Span,
) -> ast::ImplExprKind {
    match chunk {
        frontend::ImplExprPathChunk::AssocItem {
            item,
            predicate:
                frontend::Binder {
                    value: frontend::TraitPredicate { trait_ref, .. },
                    ..
                },
            index,
            ..
        } => {
            let ident = ast::ImplIdent {
                goal: trait_ref.spanned_import(span.clone()),
                name: impl_expr_name(*index as u64),
            };
            let item = item.contents().def_id.import();
            ast::ImplExprKind::Projection {
                impl_: ast::ImplExpr {
                    kind: Box::new(item_kind),
                    goal: trait_ref.spanned_import(span),
                },
                item,
                ident,
            }
        }
        frontend::ImplExprPathChunk::Parent {
            predicate:
                frontend::Binder {
                    value: frontend::TraitPredicate { trait_ref, .. },
                    ..
                },
            index,
            ..
        } => {
            let ident = ast::ImplIdent {
                goal: trait_ref.spanned_import(span.clone()),
                name: impl_expr_name(*index as u64),
            };
            ast::ImplExprKind::Parent {
                impl_: ast::ImplExpr {
                    kind: Box::new(item_kind),
                    goal: trait_ref.spanned_import(span),
                },
                ident,
            }
        }
    }
}

fn import_impl_expr_atom(
    ie: &frontend::ImplExprAtom,
    span: ast::span::Span,
    goal: ast::TraitGoal,
) -> ast::ImplExprKind {
    match ie {
        frontend::ImplExprAtom::Concrete(item_ref) => {
            ast::ImplExprKind::Concrete(item_ref.spanned_import(span))
        }
        frontend::ImplExprAtom::LocalBound { index, path, .. } => {
            let mut kind = ast::ImplExprKind::LocalBound {
                id: impl_expr_name(*index as u64),
            };
            for chunk in path {
                kind = browse_path(kind, chunk, span.clone())
            }
            kind
        }
        frontend::ImplExprAtom::SelfImpl { path, .. } => {
            let mut kind = ast::ImplExprKind::Self_;
            for chunk in path {
                kind = browse_path(kind, chunk, span.clone())
            }
            kind
        }
        frontend::ImplExprAtom::Dyn => ast::ImplExprKind::Dyn,
        frontend::ImplExprAtom::Builtin { .. } => ast::ImplExprKind::Builtin(goal),
        frontend::ImplExprAtom::Error(msg) => todo!("{}", msg), // TODO proper error
    }
}

impl SpannedImport<ast::ImplExpr> for frontend::ImplExpr {
    fn spanned_import(&self, span: ast::span::Span) -> ast::ImplExpr {
        let goal = self.r#trait.value.spanned_import(span.clone());
        let impl_ = ast::ImplExpr {
            kind: Box::new(import_impl_expr_atom(
                &self.r#impl,
                span.clone(),
                goal.clone(),
            )),
            goal: goal.clone(),
        };
        match &self.r#impl {
            frontend::ImplExprAtom::Concrete(item_ref) if !item_ref.impl_exprs.is_empty() => {
                let args = item_ref
                    .impl_exprs
                    .iter()
                    .map(|ie| ie.spanned_import(span.clone()))
                    .collect();
                ast::ImplExpr {
                    kind: Box::new(ast::ImplExprKind::ImplApp { impl_, args }),
                    goal,
                }
            }
            _ => impl_,
        }
    }
}

fn cast_of_enum(
    type_id: ast::GlobalId,
    generics: &ast::Generics,
    ty: ast::Ty,
    span: ast::span::Span,
    variants: &Vec<ast::Variant>,
) -> ast::Item {
    todo!() // TODO refactor Implement to evaluate what is needed in #1763
}

fn expect_body<Body>(optional: &Option<Body>) -> &Body {
    optional.as_ref().expect("Expected body") // TODO proper hax error
}

use std::collections::HashMap;

pub fn import_item(
    item: &frontend::FullDef<frontend::ThirBody>,
    all_items: &HashMap<frontend::DefId, &frontend::FullDef<frontend::ThirBody>>,
) -> Vec<ast::Item> {
    let frontend::FullDef {
        this,
        span,
        source_span,
        source_text,
        attributes,
        visibility,
        lang_item,
        diagnostic_item,
        kind,
    } = item;
    let ident = this.contents().def_id.clone().import();
    let span = span.import();
    let mut items = Vec::new();
    let kind = match kind {
        frontend::FullDefKind::Adt {
            param_env,
            adt_kind,
            variants,
            ..
        } => {
            let generics = param_env.import();
            let variants = variants.import();
            if let frontend::AdtKind::Enum = adt_kind {
                // TODO reactivate this when cast_of_enum is implemented
                /*  items.push(cast_of_enum(
                    ident,
                    &generics,
                    repr.typ.spanned_import(span.clone()),
                    span.clone(),
                    &variants,
                )); */
            }
            ast::ItemKind::Type {
                name: ident,
                generics,
                variants,
                is_struct: match adt_kind {
                    frontend::AdtKind::Struct => true,
                    frontend::AdtKind::Union => todo!(), // TODO proper hax error
                    frontend::AdtKind::Enum => false,
                    _ => todo!(), // TODO
                },
            }
        }
        frontend::FullDefKind::TyAlias { param_env, ty } => {
            let span: &ast::span::Span = &span;
            ast::ItemKind::TyAlias {
                name: ident,
                generics: param_env.import(),
                ty: ty.spanned_import(span.clone()),
            }
        }
        frontend::FullDefKind::ForeignTy => todo!(), // TODO proper hax error
        frontend::FullDefKind::OpaqueTy => todo!(), // TODO proper hax error (the frontend should resolve this and produce a type alias)
        frontend::FullDefKind::Trait {
            param_env,
            implied_predicates,
            self_predicate,
            items,
            ..
        } => {
            let generics = param_env.import();
            ast::ItemKind::Trait {
                name: ident,
                generics,
                items: items
                    .iter()
                    .map(|assoc_item| {
                        let item = all_items
                            .get(&assoc_item.def_id)
                            .expect("Could not find definition for associated item");
                        import_trait_item(item)
                    })
                    .collect(),
            }
        }

        frontend::FullDefKind::TraitAlias { .. } => todo!(), // TODO proper hax error
        frontend::FullDefKind::TraitImpl {
            param_env,
            trait_pred,
            implied_impl_exprs,
            items,
            ..
        } => {
            let generics = param_env.import();
            let trait_ref = trait_pred.trait_ref.contents();
            let of_trait: (ast::GlobalId, Vec<ast::GenericValue>) = (
                trait_ref.def_id.import(),
                trait_ref
                    .generic_args
                    .iter()
                    .map(|ga| ga.spanned_import(span.clone()))
                    .collect(),
            );
            let [ast::GenericValue::Ty(self_ty), ..] = &of_trait.1[..] else {
                panic!("Self should always be the first generic argument of a trait application.")
            };
            let parent_bounds = implied_impl_exprs
                .iter()
                .enumerate()
                .map(|(i, impl_expr)| {
                    let ie = impl_expr.spanned_import(span.clone());
                    let impl_ident = ast::ImplIdent {
                        goal: ie.goal.clone(),
                        name: impl_expr_name(i as u64),
                    };
                    (ie, impl_ident)
                })
                .collect();
            let items = items
                .iter()
                .map(|assoc_item| {
                    let ident = assoc_item.decl_def_id.import();
                    let assoc_item = all_items.get(&assoc_item.decl_def_id).unwrap(); // TODO error: All assoc items should be included in the list of items produced by the frontend.
                    let span = assoc_item.span.import();
                    let attributes = assoc_item.attributes.import();
                    let (generics, kind) = match assoc_item.kind() {
                        frontend::FullDefKind::AssocTy {
                            param_env, value, ..
                        } => (
                            param_env.import(),
                            ast::ImplItemKind::Type {
                                ty: expect_body(value).spanned_import(span.clone()),
                                parent_bounds: Vec::new(),
                            },
                        ), // TODO(missing) #1763 ImplExpr for associated types in trait impls (check in the item?)
                        frontend::FullDefKind::AssocFn {
                            param_env, body, ..
                        } => {
                            let body = expect_body(body);
                            (
                                param_env.import(),
                                ast::ImplItemKind::Fn {
                                    body: body.import(),
                                    params: body.params.spanned_import(span.clone()),
                                },
                            )
                        } // TODO(missing) #1763 Change TyFnSignature to add parameter binders (change the body type in THIR to be a tuple (expr,param))
                        frontend::FullDefKind::AssocConst {
                            param_env, body, ..
                        } => (
                            param_env.import(),
                            ast::ImplItemKind::Fn {
                                body: expect_body(body).import(),
                                params: Vec::new(),
                            },
                        ),
                        _ => todo!("error"), // panic!("All pointers to associated items should correspond to an actual associated item definition.")
                    };
                    ast::ImplItem {
                        meta: ast::Metadata { span, attributes },
                        generics,
                        kind,
                        ident,
                    }
                })
                .collect();
            ast::ItemKind::Impl {
                generics,
                self_ty: self_ty.clone(),
                of_trait,
                items,
                parent_bounds,
                safety: ast::SafetyKind::Safe, // TODO(missing) #1763 trait impl safety (remove from AST?)
            }
        }
        frontend::FullDefKind::InherentImpl {
            param_env, items, ..
        } => {
            return items
                    .iter()
                    .map(|assoc_item| {
                        let ident = assoc_item.def_id.import();
                        let assoc_item = all_items.get(&assoc_item.def_id).expect("All assoc items should be included in the list of items produced by the frontend.");
                        let span = assoc_item.span.import();
                        let attributes = assoc_item.attributes.import();
                        let impl_generics = param_env.import();
                        let kind = match assoc_item.kind() {
                            frontend::FullDefKind::AssocTy { param_env, value, .. } => {
                                let generics = impl_generics.clone().concat(param_env.import());
                                ast::ItemKind::TyAlias {
                                    name: ident,
                                    generics,
                                    ty: expect_body(value).spanned_import(span.clone()),
                                }
                            },
                            frontend::FullDefKind::AssocFn { param_env, sig, body , ..} => {
                                let generics = impl_generics.clone().concat(param_env.import());
                                ast::ItemKind::Fn {
                                    name: ident,
                                    generics,
                                    body: expect_body(body).import(),
                                    params: Vec::new(), // TODO(missing) #1763 Change TyFnSignature to add parameter binders
                                    safety: sig.value.safety.import(),
                                }}
                            frontend::FullDefKind::AssocConst { param_env, body, .. } =>{
                                let generics = impl_generics.clone().concat(param_env.import());
                                 ast::ItemKind::Fn {
                                    name: ident,
                                    generics,
                                    body: expect_body(body).import(),
                                    params: Vec::new(),
                                    safety: ast::SafetyKind::Safe,
                                }}
                            _ => panic!("All pointers to associated items should correspond to an actual associated item definition.")
                        };
                        ast::Item { ident, kind, meta: ast::Metadata { span, attributes } }
                    })
                    .collect();
        }
        frontend::FullDefKind::Fn {
            param_env,
            sig,
            body,
            ..
        } => {
            let body = expect_body(body);
            ast::ItemKind::Fn {
                name: ident,
                generics: param_env.import(),
                body: body.import(),
                params: body.params.spanned_import(span.clone()),
                safety: sig.value.safety.import(),
            }
        }
        frontend::FullDefKind::Closure { .. } => panic!("We should never encounter closure items"), // TODO convert to a hax error
        frontend::FullDefKind::Const {
            param_env,
            ty,
            kind,
            body,
            value,
        } => ast::ItemKind::Fn {
            name: ident,
            generics: param_env.import(),
            body: expect_body(body).import(),
            params: Vec::new(),
            safety: ast::SafetyKind::Safe,
        },
        frontend::FullDefKind::Static {
            mutability: true, ..
        } => panic!("Mutable static items are not supported."), // TODO proper hax error for issue 1343
        frontend::FullDefKind::Static {
            mutability: false,
            body,
            ..
        } => ast::ItemKind::Fn {
            name: ident,
            generics: ast::Generics {
                params: Vec::new(),
                constraints: Vec::new(),
            },
            body: expect_body(body).import(),
            params: Vec::new(),
            safety: ast::SafetyKind::Safe,
        },
        frontend::FullDefKind::ExternCrate
        | frontend::FullDefKind::Use
        | frontend::FullDefKind::TyParam
        | frontend::FullDefKind::ConstParam
        | frontend::FullDefKind::LifetimeParam
        | frontend::FullDefKind::Variant
        | frontend::FullDefKind::Ctor { .. }
        | frontend::FullDefKind::Field
        | frontend::FullDefKind::Macro(_)
        | frontend::FullDefKind::Mod { .. }
        | frontend::FullDefKind::ForeignMod { .. }
        | frontend::FullDefKind::SyntheticCoroutineBody => return Vec::new(),
        frontend::FullDefKind::GlobalAsm => panic!("Inline assembly blocks are not supported"), // TODO hax error for 1344
        frontend::FullDefKind::AssocConst { .. }
        | frontend::FullDefKind::AssocFn { .. }
        | frontend::FullDefKind::AssocTy { .. } => return Vec::new(), // These item kinds are handled by the case of Impl
    };
    items.push(ast::Item {
        ident,
        kind,
        meta: ast::Metadata {
            span,
            attributes: attributes.import(),
        },
    });
    items
}
