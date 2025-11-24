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

impl Import<ast::Attribute> for frontend::Attribute {
    fn import(&self) -> ast::Attribute {
        // TODO
        ast::Attribute {
            kind: ast::AttributeKind::Tool {
                path: "TODO".to_string(),
                tokens: "".to_string(),
            },
            span: ast::span::Span::dummy(),
        }
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
                    name: Symbol::new(format!("i{}", self.id.0)),
                }))
            }
            // TODO reimplement the same behaviour as ocaml
            frontend::ClauseKind::Projection(projection_predicate) => None,
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

impl SpannedImport<ast::Ty> for frontend::Ty {
    fn spanned_import(&self, span: ast::span::Span) -> ast::Ty {
        ast::Ty(Box::new(ast::TyKind::App {
            head: ast::GlobalId::unit_ty(),
            args: Vec::new(),
        }))
        // TODO implement
        /* let kind = match self.kind() {
            frontend::TyKind::Bool => todo!(),
            frontend::TyKind::Char => todo!(),
            frontend::TyKind::Int(int_ty) => todo!(),
            frontend::TyKind::Uint(uint_ty) => todo!(),
            frontend::TyKind::Float(float_ty) => todo!(),
            frontend::TyKind::FnDef { item, fn_sig } => todo!(),
            frontend::TyKind::Arrow(binder) => todo!(),
            frontend::TyKind::Closure(closure_args) => todo!(),
            frontend::TyKind::Adt(item_ref) => todo!(),
            frontend::TyKind::Foreign(item_ref) => todo!(),
            frontend::TyKind::Str => todo!(),
            frontend::TyKind::Array(ty, decorated) => todo!(),
            frontend::TyKind::Slice(ty) => todo!(),
            frontend::TyKind::RawPtr(ty, _) => todo!(),
            frontend::TyKind::Ref(region, ty, _) => todo!(),
            frontend::TyKind::Dynamic(param_ty, generic_predicates, region) => todo!(),
            frontend::TyKind::Coroutine(item_ref) => todo!(),
            frontend::TyKind::Never => todo!(),
            frontend::TyKind::Tuple(items) => ast::TyKind::App {
                head: ast::GlobalId::unit_ty(),
                args: Vec::new(),
            },
            frontend::TyKind::Alias(alias) => todo!(),
            frontend::TyKind::Param(param_ty) => todo!(),
            frontend::TyKind::Bound(_, bound_ty) => todo!(),
            frontend::TyKind::Placeholder(placeholder) => todo!(),
            frontend::TyKind::Infer(infer_ty) => todo!(),
            frontend::TyKind::Error => todo!(),
            frontend::TyKind::Todo(_) => todo!(),
        };
        ast::Ty(Box::new(kind)) */
    }
}

impl Import<ast::Expr> for frontend::Expr {
    fn import(&self) -> ast::Expr {
        let Self {
            ty,
            span,
            contents,
            hir_id,
            attributes,
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

impl Import<ast::TraitItem> for frontend::AssocItem {
    fn import(&self) -> ast::TraitItem {
        // TODO refactor and inline or inject context
        let meta = ast::Metadata {
            span: ast::span::Span::dummy(),
            attributes: Vec::new(),
        };
        let generics = ast::Generics {
            params: Vec::new(),
            constraints: Vec::new(),
        };
        let kind = match &self.kind {
            _ if self.has_value => ast::TraitItemKind::Default {
                params: todo!(),
                body: todo!(),
            },
            frontend::AssocKind::Const { name } => ast::TraitItemKind::Fn(todo!()),
            frontend::AssocKind::Fn { name, has_self } => ast::TraitItemKind::Fn(todo!()),
            frontend::AssocKind::Type { data } => ast::TraitItemKind::Type(todo!()),
        };
        ast::TraitItem {
            meta,
            kind,
            generics,
            ident: self.def_id.import(),
        }
    }
}

impl SpannedImport<ast::TraitGoal> for frontend::TraitRef {
    fn spanned_import(&self, span: ast::span::Span) -> ast::TraitGoal {
        let trait_ = self.def_id.import();
        let args = self.generic_args.spanned_import(span);
        ast::TraitGoal { trait_, args }
    }
}

impl SpannedImport<ast::ImplExprKind> for frontend::ImplExprAtom {
    // TODO refactor this needs the goal so it should not be a trait impl
    fn spanned_import(&self, span: ast::span::Span) -> ast::ImplExprKind {
        match self {
            frontend::ImplExprAtom::Concrete(item_ref) => {
                ast::ImplExprKind::Concrete(item_ref.spanned_import(span))
            }
            frontend::ImplExprAtom::LocalBound { index, path, .. } => todo!(),
            frontend::ImplExprAtom::SelfImpl { r#trait, path } => todo!(),
            frontend::ImplExprAtom::Dyn => ast::ImplExprKind::Dyn,
            frontend::ImplExprAtom::Builtin {
                trait_data,
                impl_exprs,
                types,
            } => todo!(),
            frontend::ImplExprAtom::Error(_) => todo!(),
        }
    }
}

impl SpannedImport<ast::ImplExpr> for frontend::ImplExpr {
    fn spanned_import(&self, span: ast::span::Span) -> ast::ImplExpr {
        let goal = self.r#trait.value.spanned_import(span.clone());
        let impl_ = ast::ImplExpr {
            kind: Box::new(self.r#impl.spanned_import(span.clone())),
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
    item: &frontend::FullDef<frontend::Expr>,
    all_items: &HashMap<frontend::DefId, &frontend::FullDef<frontend::Expr>>,
) -> Vec<ast::Item> {
    let frontend::FullDef::<frontend::Expr> {
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
            flags,
            repr,
            drop_glue,
            drop_impl,
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
        } => {
            let generics = param_env.import();
            ast::ItemKind::Trait {
                name: ident,
                generics,
                items: items.iter().map(frontend::AssocItem::import).collect(),
            }
        }

        frontend::FullDefKind::TraitAlias {
            param_env,
            implied_predicates,
            self_predicate,
        } => todo!(), // TODO proper hax error
        frontend::FullDefKind::TraitImpl {
            param_env,
            trait_pred,
            implied_impl_exprs,
            items,
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
                .filter_map(|impl_expr| {
                    None // TODO the clause we need here comes from param_env
                })
                .collect();
            let items = items.iter().map(|assoc_item| {
                let ident = assoc_item.decl_def_id.import();
                let assoc_item = all_items.get(&assoc_item.decl_def_id).expect("All assoc items should be included in the list of items produced by the frontend.");
                let span = assoc_item.span.import();
                let attributes = assoc_item.attributes.import();
                let (generics, kind) = match assoc_item.kind() {
                    hax_frontend_exporter::FullDefKind::AssocTy { param_env, value, .. } =>
                      (param_env.import(), ast::ImplItemKind::Type { ty: expect_body(value).spanned_import(span.clone()), parent_bounds: Vec::new() }),// TODO(missing) #1763 ImplExpr for associated types in trait impls
                    hax_frontend_exporter::FullDefKind::AssocFn { param_env, body, .. } =>
                       (param_env.import(), ast::ImplItemKind::Fn { body: expect_body(body).import(), params: Vec::new() }),// TODO(missing) #1763 Change TyFnSignature to add parameter binders
                    hax_frontend_exporter::FullDefKind::AssocConst { param_env, associated_item, ty, body } =>
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
                safety: ast::SafetyKind::Safe, // TODO(missing) #1763 trait impl safety
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
        frontend::FullDefKind::Closure {
            args,
            is_const,
            fn_once_impl,
            fn_mut_impl,
            fn_impl,
            once_shim,
            drop_glue,
            drop_impl,
        } => panic!("We should never encounter closure items"), // TODO convert to a hax error
        frontend::FullDefKind::Const {
            param_env,
            ty,
            kind,
            body,
        } => ast::ItemKind::Fn {
            name: ident,
            generics: param_env.import(),
            body: expect_body(body).import(),
            params: Vec::new(),
            safety: ast::SafetyKind::Safe,
        },
        frontend::FullDefKind::Static {
            param_env,
            safety,
            mutability,
            nested,
            ty,
            body,
        } => todo!(),
        frontend::FullDefKind::ExternCrate
        | frontend::FullDefKind::Use
        | frontend::FullDefKind::TyParam
        | frontend::FullDefKind::ConstParam
        | frontend::FullDefKind::LifetimeParam
        | frontend::FullDefKind::Variant
        | frontend::FullDefKind::Ctor { .. }
        | frontend::FullDefKind::Field
        | frontend::FullDefKind::Macro(_) => return Vec::new(),
        frontend::FullDefKind::Mod { items } => todo!(),
        frontend::FullDefKind::ForeignMod { items } => todo!(),
        frontend::FullDefKind::GlobalAsm => todo!(),
        frontend::FullDefKind::SyntheticCoroutineBody => todo!(),
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
