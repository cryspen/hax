use crate::ast;
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

impl SpannedImport<Vec<ast::GenericValue>> for Vec<frontend::GenericArg> {
    fn spanned_import(&self, span: ast::span::Span) -> Vec<ast::GenericValue> {
        self.iter()
            .map(|ga| ga.spanned_import(span.clone()))
            .collect()
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
            frontend::TyKind::Tuple(items) => unit_ty(), //  TODO helper
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
            let items = items.iter().map(|assoc_item| {
                let ident = assoc_item.decl_def_id.import();
                let assoc_item = all_items.get(&assoc_item.decl_def_id).expect("All assoc items should be included in the list of items produced by the frontend.");
                let span = assoc_item.span.import();
                let attributes = assoc_item.attributes.import();
                let (generics, kind) = match assoc_item.kind() {
                    frontend::FullDefKind::AssocTy { param_env, value, .. } =>
                      (param_env.import(), ast::ImplItemKind::Type { ty: expect_body(value).spanned_import(span.clone()), parent_bounds: Vec::new() }),// TODO(missing) #1763 ImplExpr for associated types in trait impls (check in the item?)
                    frontend::FullDefKind::AssocFn { param_env, body, .. } =>
                       (param_env.import(), ast::ImplItemKind::Fn { body: expect_body(body).import(), params: Vec::new() }),// TODO(missing) #1763 Change TyFnSignature to add parameter binders (change the body type in THIR to be a tuple (expr,param))
                    frontend::FullDefKind::AssocConst { param_env, body, .. } =>
                      (param_env.import(), ast::ImplItemKind::Fn { body: expect_body(body).import(), params: Vec::new() }),
                    _ => panic!("All pointers to associated items should correspond to an actual associated item definition.")
                };
                ast::ImplItem {
                    meta: ast::Metadata { span, attributes },
                    generics,
                    kind,
                    ident,
                }
            }).collect();
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
            ast::ItemKind::Fn {
                name: ident,
                generics: param_env.import(),
                body: expect_body(body).import(),
                params: Vec::new(), // TODO(missing) #1763 Change TyFnSignature to add parameter binders
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
