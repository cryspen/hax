//! This modules allows to import the THIR AST produced by the frontend, and convert it to the engine's internal AST

use crate::ast;
use crate::symbol::Symbol;
use hax_frontend_exporter as frontend;

fn unsupported(msg: &str, issue_id: u32, span: &ast::span::Span) -> ast::ErrorNode {
    let fragment = ast::fragment::Fragment::Unknown(msg.to_owned());
    let diagnostic = ast::diagnostics::Diagnostic::new(
        fragment.clone(),
        ast::diagnostics::DiagnosticInfo {
            context: ast::diagnostics::Context::Import,
            span: span.clone(),
            kind: hax_types::diagnostics::Kind::Unimplemented {
                issue_id: Some(issue_id),
                details: Some(msg.to_owned()),
            },
        },
    );
    ast::ErrorNode {
        fragment: Box::new(fragment),
        diagnostics: vec![diagnostic],
    }
}
fn failure(msg: &str, span: &ast::span::Span) -> ast::ErrorNode {
    let fragment = ast::fragment::Fragment::Unknown(msg.to_owned());
    let diagnostic = ast::diagnostics::Diagnostic::new(
        fragment.clone(),
        ast::diagnostics::DiagnosticInfo {
            context: ast::diagnostics::Context::Import,
            span: span.clone(),
            kind: hax_types::diagnostics::Kind::AssertionFailure {
                details: msg.to_owned(),
            },
        },
    );
    ast::ErrorNode {
        fragment: Box::new(fragment),
        diagnostics: vec![diagnostic],
    }
}

trait SpannedImport<Out> {
    fn spanned_import(&self, span: ast::span::Span) -> Out;
}

trait Import<Out> {
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

fn import_fn_sig(fn_sig: &frontend::TyFnSig, span: ast::span::Span) -> ast::TyKind {
    let inputs = if fn_sig.inputs.is_empty() {
        vec![ast::Ty(Box::new(ast::TyKind::unit()))]
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
            frontend::TyKind::Foreign(..) => {
                ast::TyKind::Error(unsupported("Foreign type", 928, &span))
            }
            frontend::TyKind::Str => ast::TyKind::Primitive(ast::PrimitiveTy::Str),
            frontend::TyKind::Array(item_ref) => {
                if let [
                    frontend::GenericArg::Type(ty),
                    frontend::GenericArg::Const(length),
                ] = &item_ref.generic_args[..]
                {
                    ast::TyKind::Array {
                        ty: ty.spanned_import(span.clone()),
                        length: Box::new(length.import()),
                    }
                } else {
                    ast::TyKind::Error(failure(
                        "Wrong generics for array: expected a type and a constant. See synthetic_items in hax frontend.",
                        &span,
                    ))
                }
            }
            frontend::TyKind::Slice(ty) => {
                if let [frontend::GenericArg::Type(ty)] = &ty.generic_args[..] {
                    ast::TyKind::Slice(ty.spanned_import(span.clone()))
                } else {
                    ast::TyKind::Error(failure(
                        "Wrong generics for slice: expected a type. See synthetic_items in hax frontend.",
                        &span,
                    ))
                }
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
                        }) => Ok(ast::DynTraitGoal {
                            trait_: trait_ref.def_id.import(),
                            non_self_args: trait_ref.generic_args.spanned_import(span.clone())[1..]
                                .to_vec(),
                        }),
                        _ => Err(failure("type Dyn with non trait predicate", &span)),
                    })
                    .collect::<Result<Vec<_>, _>>();
                match goals {
                    Ok(goals) => ast::TyKind::Dyn(goals),
                    Err(e) => ast::TyKind::Error(e),
                }
            }
            frontend::TyKind::Coroutine(_) => {
                ast::TyKind::Error(unsupported("Coroutine type", 924, &span))
            }
            frontend::TyKind::Never => ast::TyKind::App {
                head: crate::names::rust_primitives::hax::Never,
                args: Vec::new(),
            },
            frontend::TyKind::Tuple(items) => {
                let args = items.generic_args.spanned_import(span.clone());
                ast::TyKind::tuple(args)
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
            }) => ast::TyKind::Error(failure("Ty::Alias with AliasTyKind::Inherent", &span)),
            frontend::TyKind::Alias(frontend::Alias {
                kind: frontend::AliasKind::Free,
                ..
            }) => ast::TyKind::Error(failure("Ty::Alias with AliasTyKind::Free", &span)),
            frontend::TyKind::Param(frontend::ParamTy { name, .. }) => {
                ast::TyKind::Param(ast::LocalId(Symbol::new(name.clone())))
            }
            frontend::TyKind::Bound(..) => ast::TyKind::Error(failure(
                "type Bound: should be gone after typechecking",
                &span,
            )),
            frontend::TyKind::Placeholder(..) => ast::TyKind::Error(failure(
                "type Placeholder: should be gone after typechecking",
                &span,
            )),
            frontend::TyKind::Infer(..) => ast::TyKind::Error(failure(
                "type Infer: should be gone after typechecking",
                &span,
            )),
            frontend::TyKind::Error => ast::TyKind::Error(failure(
                "got type `Error`: Rust compilation probably failed.",
                &span,
            )),
            frontend::TyKind::Todo(_) => ast::TyKind::Error(failure("type Todo", &span)),
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
            frontend::ConstantLiteral::ByteStr(items) => todo!(), // TODO deal with this by returning an "extendedliteral", or return an expr_kind here
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
        let kind = match contents.as_ref() {
            frontend::ConstantExprKind::Literal(constant_literal) => todo!(),
            frontend::ConstantExprKind::Adt { info, fields } => todo!(),
            frontend::ConstantExprKind::Array { fields } => todo!(),
            frontend::ConstantExprKind::Tuple { fields } => todo!(),
            frontend::ConstantExprKind::GlobalName(item_ref) => todo!(),
            frontend::ConstantExprKind::TraitConst { impl_expr, name } => todo!(),
            frontend::ConstantExprKind::Borrow(decorated) => todo!(),
            frontend::ConstantExprKind::RawBorrow { mutability, arg } => todo!(),
            frontend::ConstantExprKind::Cast { source } => todo!(),
            frontend::ConstantExprKind::ConstRef { id } => todo!(),
            frontend::ConstantExprKind::FnPtr(item_ref) => todo!(),
            frontend::ConstantExprKind::Memory(items) => todo!(),
            frontend::ConstantExprKind::Todo(_) => todo!(),
        };
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
        let kind = match contents.as_ref() {
            frontend::ExprKind::Box { value } => todo!(),
            frontend::ExprKind::If {
                if_then_scope,
                cond,
                then,
                else_opt,
            } => todo!(),
            frontend::ExprKind::Call {
                ty,
                fun,
                args,
                from_hir_call,
                fn_span,
            } => todo!(),
            frontend::ExprKind::Deref { arg } => todo!(),
            frontend::ExprKind::Binary { op, lhs, rhs } => todo!(),
            frontend::ExprKind::LogicalOp { op, lhs, rhs } => todo!(),
            frontend::ExprKind::Unary { op, arg } => todo!(),
            frontend::ExprKind::Cast { source } => todo!(),
            frontend::ExprKind::Use { source } => todo!(),
            frontend::ExprKind::NeverToAny { source } => todo!(),
            frontend::ExprKind::PointerCoercion { cast, source } => todo!(),
            frontend::ExprKind::Loop { body } => todo!(),
            frontend::ExprKind::Match { scrutinee, arms } => todo!(),
            frontend::ExprKind::Let { expr, pat } => todo!(),
            frontend::ExprKind::Block { block } => {
                return block.expr.as_ref().unwrap().import();
            }
            frontend::ExprKind::Assign { lhs, rhs } => todo!(),
            frontend::ExprKind::AssignOp { op, lhs, rhs } => todo!(),
            frontend::ExprKind::Field { field, lhs } => todo!(),
            frontend::ExprKind::TupleField { field, lhs } => todo!(),
            frontend::ExprKind::Index { lhs, index } => todo!(),
            frontend::ExprKind::VarRef { id } => todo!(),
            frontend::ExprKind::ConstRef { id } => todo!(),
            frontend::ExprKind::GlobalName { item, constructor } => todo!(),
            frontend::ExprKind::UpvarRef {
                closure_def_id,
                var_hir_id,
            } => todo!(),
            frontend::ExprKind::Borrow { borrow_kind, arg } => todo!(),
            frontend::ExprKind::RawBorrow { mutability, arg } => todo!(),
            frontend::ExprKind::Break { label, value } => todo!(),
            frontend::ExprKind::Continue { label } => todo!(),
            frontend::ExprKind::Return { value } => todo!(),
            frontend::ExprKind::ConstBlock(item_ref) => todo!(),
            frontend::ExprKind::Repeat { value, count } => todo!(),
            frontend::ExprKind::Array { fields } => todo!(),
            frontend::ExprKind::Tuple { fields } => ast::ExprKind::Construct {
                constructor: ast::GlobalId::unit_constructor(),
                is_record: false,
                is_struct: true,
                fields: Vec::new(),
                base: None,
            },
            frontend::ExprKind::Adt(adt_expr) => todo!(),
            frontend::ExprKind::PlaceTypeAscription { source, user_ty } => todo!(),
            frontend::ExprKind::ValueTypeAscription { source, user_ty } => todo!(),
            frontend::ExprKind::Closure {
                params,
                body,
                upvars,
                movability,
            } => todo!(),
            frontend::ExprKind::Literal { lit, neg } => todo!(),
            frontend::ExprKind::ZstLiteral { user_ty } => todo!(),
            frontend::ExprKind::NamedConst { item, user_ty } => todo!(),
            frontend::ExprKind::ConstParam { param, def_id } => todo!(),
            frontend::ExprKind::StaticRef {
                alloc_id,
                ty,
                def_id,
            } => todo!(),
            frontend::ExprKind::Yield { value } => todo!(),
            frontend::ExprKind::Todo(_) => todo!(),
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
        todo!()
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
        // TODO
        ast::Pat {
            kind: Box::new(ast::PatKind::Wild),
            ty: ty.spanned_import(span.clone()),
            meta: ast::Metadata {
                span,
                attributes: vec![],
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
        } => ast::TraitItemKind::Error(failure(
            "Associate types defaults are not supported by hax yet (it is a nightly feature)",
            &span,
        )),
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
        _ => ast::TraitItemKind::Error(failure("Found associated item of an unknown kind.", &span)),
    };
    let (frontend::FullDefKind::AssocConst { param_env, .. }
    | frontend::FullDefKind::AssocFn { param_env, .. }
    | frontend::FullDefKind::AssocTy { param_env, .. }) = &item.kind
    else {
        unreachable!("Found associated item of an unknown kind.")
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
        frontend::ImplExprAtom::Error(msg) => ast::ImplExprKind::Error(failure(msg, &span)),
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

fn generic_param_to_value(p: &ast::GenericParam) -> ast::GenericValue {
    match &p.kind {
        ast::GenericParamKind::Lifetime => ast::GenericValue::Lifetime,
        ast::GenericParamKind::Type => {
            ast::GenericValue::Ty(ast::TyKind::Param(p.ident.clone()).promote())
        }
        ast::GenericParamKind::Const { ty } => ast::GenericValue::Expr(
            ast::ExprKind::LocalId(p.ident.clone()).promote(ty.clone(), p.meta.span.clone()),
        ),
    }
}

fn cast_of_enum(
    type_id: ast::GlobalId,
    generics: &ast::Generics,
    ty: ast::Ty,
    span: ast::span::Span,
    variants: &Vec<(ast::Variant, frontend::VariantDef)>,
) -> ast::Item {
    let type_ref = ast::TyKind::App {
        head: type_id,
        args: generics.params.iter().map(generic_param_to_value).collect(),
    }
    .promote();
    let name = ast::GlobalId::with_suffix(type_id, ast::global_id::ReservedSuffix::Cast);
    let ast::TyKind::Primitive(ast::PrimitiveTy::Int(int_kind)) = &*ty.0 else {
        return ast::ItemKind::Error(failure(
            &format!("cast_of_enum: expected int type, got {:?}", ty),
            &span,
        ))
        .promote(name, span);
    };
    let mut arms = Vec::new();
    let mut previous_explicit_determinator = None;
    for (variant, variant_def) in variants {
        // Each variant comes with a [rustc_middle::ty::VariantDiscr]. Some variant have [Explicit] discr (i.e. an expression)
        // while other have [Relative] discr (the distance to the previous last explicit discr).
        let body = match &variant_def.discr_def {
            frontend::DiscriminantDefinition::Relative(m) => {
                ast::ExprKind::Literal(ast::literals::Literal::Int {
                    value: Symbol::new(m.to_string()),
                    negative: false,
                    kind: int_kind.clone(),
                })
                .promote(ty.clone(), span.clone())
            }
            frontend::DiscriminantDefinition::Explicit(did) => {
                let e = ast::ExprKind::GlobalId(did.import()).promote(ty.clone(), span.clone());
                previous_explicit_determinator = Some(e.clone());
                e
            }
        };
        let pat = ast::PatKind::Construct {
            constructor: variant.name,
            is_record: variant.is_record,
            is_struct: false,
            fields: variant
                .arguments
                .iter()
                .map(|(cid, ty, _)| (*cid, ast::PatKind::Wild.promote(ty.clone(), span.clone())))
                .collect(),
        }
        .promote(ty.clone(), span.clone());
        arms.push(ast::Arm::non_guarded(pat, body, span.clone()));
    }
    let scrutinee_var = ast::LocalId(Symbol::new("x"));
    let scrutinee =
        ast::ExprKind::LocalId(scrutinee_var.clone()).promote(type_ref.clone(), span.clone());
    let params = vec![ast::Param {
        pat: ast::PatKind::var_pat(scrutinee_var).promote(type_ref, span.clone()),
        ty: ty.clone(),
        ty_span: None,
        attributes: Vec::new(),
    }];
    let body = ast::ExprKind::Match { scrutinee, arms }.promote(ty, span.clone());
    ast::ItemKind::Fn {
        name: name.clone(),
        generics: generics.clone(),
        body,
        params,
        safety: ast::SafetyKind::Safe,
    }
    .promote(name, span)
}

fn expect_body<'a, Body>(
    optional: &'a Option<Body>,
    span: &ast::span::Span,
) -> Result<&'a Body, ast::ErrorNode> {
    optional.as_ref().ok_or(failure("Expected body", span))
}

use std::collections::HashMap;

/// Import a `FullDef` item produced by the frontend, and produce the corresponding item
/// (or items for inherent impls)
pub fn import_item(
    item: &frontend::FullDef<frontend::ThirBody>,
    all_items: &HashMap<frontend::DefId, &frontend::FullDef<frontend::ThirBody>>,
) -> Vec<ast::Item> {
    let frontend::FullDef {
        this,
        span,
        attributes,
        kind,
        ..
    } = item;
    let ident = this.contents().def_id.clone().import();
    let span = span.import();
    let mut items = Vec::new();
    let kind = match kind {
        frontend::FullDefKind::Adt {
            param_env,
            adt_kind,
            variants,
            repr,
            ..
        } => {
            let generics = param_env.import();
            let variants_with_def: Vec<(ast::Variant, frontend::VariantDef)> = variants
                .clone()
                .into_iter()
                .map(|v| (v.import(), v))
                .collect();
            let variants = variants_with_def.iter().map(|(v, _)| v.clone()).collect();
            let res_kind = match adt_kind {
                frontend::AdtKind::Union => {
                    ast::ItemKind::Error(unsupported("Union type", 998, &span))
                }
                frontend::AdtKind::Enum | frontend::AdtKind::Struct => ast::ItemKind::Type {
                    name: ident,
                    generics: generics.clone(),
                    variants,
                    is_struct: match adt_kind {
                        frontend::AdtKind::Enum => false,
                        frontend::AdtKind::Struct => true,
                        _ => unreachable!(),
                    },
                },
                frontend::AdtKind::Array => ast::ItemKind::Error(failure("Array ADT type", &span)),
                frontend::AdtKind::Slice => ast::ItemKind::Error(failure("Slice ADT type", &span)),
                frontend::AdtKind::Tuple => ast::ItemKind::Error(failure("Tuple ADT type", &span)),
            };
            if let frontend::AdtKind::Enum = adt_kind {
                // TODO discs
                let cast_item = cast_of_enum(
                    ident,
                    &generics,
                    repr.typ.spanned_import(span.clone()),
                    span.clone(),
                    &variants_with_def,
                );
                return vec![res_kind.promote(ident, span), cast_item];
            } else {
                res_kind
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
        frontend::FullDefKind::ForeignTy => {
            ast::ItemKind::Error(unsupported("Foreign type", 928, &span))
        }
        frontend::FullDefKind::OpaqueTy => ast::ItemKind::Error(failure(
            "OpaqueTy should be replaced by Alias in the frontend",
            &span,
        )),
        frontend::FullDefKind::Trait {
            param_env,
            implied_predicates,
            items,
            ..
        } => {
            let mut generics = param_env.import();
            let mut implied_predicates = implied_predicates.import();
            generics.constraints.append(&mut implied_predicates);
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
                safety: ast::SafetyKind::Safe, // TODO(missing) #1763 add safety to traits in the frontend
            }
        }

        frontend::FullDefKind::TraitAlias { .. } => {
            ast::ItemKind::Error(failure("Trait Alias", &span))
        }
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
            let items = items.iter().map(|assoc_item| {
                let ident = assoc_item.decl_def_id.import();
                let assoc_item = all_items.get(&assoc_item.decl_def_id).expect("All assoc items should be included in the list of items produced by the frontend.");
                let span = assoc_item.span.import();
                let attributes = assoc_item.attributes.import();
                let (generics, kind) = match assoc_item.kind() {
                    frontend::FullDefKind::AssocTy { param_env, value, .. } =>
                    (param_env.import(),match expect_body(value, &span) {
                      Ok(body) =>  ast::ImplItemKind::Type { ty: body.spanned_import(span.clone()), parent_bounds: Vec::new() },
                      Err(error) => ast::ImplItemKind::Error(error),
                    }),// TODO(missing) #1763 ImplExpr for associated types in trait impls (check in the item?)
                    frontend::FullDefKind::AssocFn { param_env, body, .. } =>
                       (param_env.import(), match expect_body(body, &span) { Ok(body) =>
                        ast::ImplItemKind::Fn { body: body.import(), params: body.params.spanned_import(span.clone()) }, Err(error) => ast::ImplItemKind::Error(error)}),
                    frontend::FullDefKind::AssocConst { param_env, body, .. } =>
                      (param_env.import(), match expect_body(body, &span) { Ok(body) =>ast::ImplItemKind::Fn { body: body.import(), params: Vec::new() },
                    Err(error) => ast::ImplItemKind::Error(error)}
                    ),
                    _ => unreachable!("All pointers to associated items should correspond to an actual associated item definition.")
                };
                ast::ImplItem {
                    meta: ast::Metadata { span, attributes },
                    generics,
                    kind,
                    ident,
                }
            }).collect();

            if let [ast::GenericValue::Ty(self_ty), ..] = &of_trait.1[..] {
                ast::ItemKind::Impl {
                    generics,
                    self_ty: self_ty.clone(),
                    of_trait,
                    items,
                    parent_bounds,
                }
            } else {
                ast::ItemKind::Error(failure(
                    "Self should always be the first generic argument of a trait application.",
                    &span,
                ))
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
                                match expect_body(value, &span) {
                                    Ok(body) => ast::ItemKind::TyAlias {
                                    name: ident,
                                    generics,
                                    ty: body.spanned_import(span.clone()),
                                },
                                Err(err) => ast::ItemKind::Error(err)
                                }
                            },
                            frontend::FullDefKind::AssocFn { param_env, sig, body , ..} => {
                                let generics = impl_generics.clone().concat(param_env.import());
                                match expect_body(body, &span) {
                                    Ok(body) =>ast::ItemKind::Fn {
                                    name: ident,
                                    generics,
                                    body: body.import(),
                                    params: body.params.spanned_import(span.clone()),
                                    safety: sig.value.safety.import(),
                                },
                                Err(err) => ast::ItemKind::Error(err)
                                }}
                            frontend::FullDefKind::AssocConst { param_env, body, .. } => {
                                let generics = impl_generics.clone().concat(param_env.import());
                                match expect_body(body, &span) {
                                    Ok(body) => ast::ItemKind::Fn {
                                    name: ident,
                                    generics,
                                    body: body.import(),
                                    params: Vec::new(),
                                    safety: ast::SafetyKind::Safe,
                                },
                                Err(err) => ast::ItemKind::Error(err)
                                }}
                            _ => ast::ItemKind::Error(failure("All pointers to associated items should correspond to an actual associated item definition.", &span))
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
        } => match expect_body(body, &span) {
            Ok(body) => ast::ItemKind::Fn {
                name: ident,
                generics: param_env.import(),
                body: body.import(),
                params: body.params.spanned_import(span.clone()),
                safety: sig.value.safety.import(),
            },
            Err(err) => ast::ItemKind::Error(err),
        },
        frontend::FullDefKind::Closure { .. } => {
            ast::ItemKind::Error(failure("Closure item", &span))
        }
        frontend::FullDefKind::Const {
            param_env, body, ..
        } => match expect_body(body, &span) {
            Ok(body) => ast::ItemKind::Fn {
                name: ident,
                generics: param_env.import(),
                body: body.import(),
                params: Vec::new(),
                safety: ast::SafetyKind::Safe,
            },
            Err(err) => ast::ItemKind::Error(err),
        },
        frontend::FullDefKind::Static {
            mutability: true, ..
        } => ast::ItemKind::Error(unsupported("Mutable static item", 1343, &span)),
        frontend::FullDefKind::Static {
            mutability: false,
            body,
            ..
        } => match expect_body(body, &span) {
            Ok(body) => ast::ItemKind::Fn {
                name: ident,
                generics: ast::Generics {
                    params: Vec::new(),
                    constraints: Vec::new(),
                },
                body: body.import(),
                params: Vec::new(),
                safety: ast::SafetyKind::Safe,
            },
            Err(err) => ast::ItemKind::Error(err),
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
        frontend::FullDefKind::GlobalAsm => {
            ast::ItemKind::Error(unsupported("Inline assembly item", 1344, &span))
        }
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
