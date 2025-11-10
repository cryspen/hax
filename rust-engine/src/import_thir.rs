use crate::ast;
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
        todo!()
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
            ident: ast::LocalId(crate::symbol::Symbol::new(name.clone())),
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
            hax_frontend_exporter::GenericArg::Lifetime(_) => ast::GenericValue::Lifetime,
            hax_frontend_exporter::GenericArg::Type(ty) => {
                ast::GenericValue::Ty(ty.spanned_import(span))
            }
            hax_frontend_exporter::GenericArg::Const(decorated) => {
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
                let args = trait_predicate
                    .trait_ref
                    .generic_args
                    .iter()
                    .map(|ga| ga.spanned_import(span.clone()))
                    .collect();
                let trait_ = trait_predicate.trait_ref.def_id.import();
                let goal = ast::TraitGoal { trait_, args };

                Some(ast::GenericConstraint::Type(ast::ImplIdent {
                    goal,
                    name: crate::symbol::Symbol::new(format!("i{}", self.id.0)),
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
            hax_frontend_exporter::Safety::Unsafe => ast::SafetyKind::Unsafe,
            hax_frontend_exporter::Safety::Safe => ast::SafetyKind::Safe,
        }
    }
}

impl SpannedImport<ast::Ty> for frontend::Ty {
    fn spanned_import(&self, span: ast::span::Span) -> ast::Ty {
        let kind = match self.kind() {
            hax_frontend_exporter::TyKind::Bool => todo!(),
            hax_frontend_exporter::TyKind::Char => todo!(),
            hax_frontend_exporter::TyKind::Int(int_ty) => todo!(),
            hax_frontend_exporter::TyKind::Uint(uint_ty) => todo!(),
            hax_frontend_exporter::TyKind::Float(float_ty) => todo!(),
            hax_frontend_exporter::TyKind::FnDef { item, fn_sig } => todo!(),
            hax_frontend_exporter::TyKind::Arrow(binder) => todo!(),
            hax_frontend_exporter::TyKind::Closure(closure_args) => todo!(),
            hax_frontend_exporter::TyKind::Adt(item_ref) => todo!(),
            hax_frontend_exporter::TyKind::Foreign(item_ref) => todo!(),
            hax_frontend_exporter::TyKind::Str => todo!(),
            hax_frontend_exporter::TyKind::Array(ty, decorated) => todo!(),
            hax_frontend_exporter::TyKind::Slice(ty) => todo!(),
            hax_frontend_exporter::TyKind::RawPtr(ty, _) => todo!(),
            hax_frontend_exporter::TyKind::Ref(region, ty, _) => todo!(),
            hax_frontend_exporter::TyKind::Dynamic(param_ty, generic_predicates, region) => todo!(),
            hax_frontend_exporter::TyKind::Coroutine(item_ref) => todo!(),
            hax_frontend_exporter::TyKind::Never => todo!(),
            hax_frontend_exporter::TyKind::Tuple(items) => ast::TyKind::App {
                head: ast::GlobalId::unit_ty(),
                args: Vec::new(),
            },
            hax_frontend_exporter::TyKind::Alias(alias) => todo!(),
            hax_frontend_exporter::TyKind::Param(param_ty) => todo!(),
            hax_frontend_exporter::TyKind::Bound(_, bound_ty) => todo!(),
            hax_frontend_exporter::TyKind::Placeholder(placeholder) => todo!(),
            hax_frontend_exporter::TyKind::Infer(infer_ty) => todo!(),
            hax_frontend_exporter::TyKind::Error => todo!(),
            hax_frontend_exporter::TyKind::Todo(_) => todo!(),
        };
        ast::Ty(Box::new(kind))
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
        let kind = match contents.as_ref() {
            hax_frontend_exporter::ExprKind::Box { value } => todo!(),
            hax_frontend_exporter::ExprKind::If {
                if_then_scope,
                cond,
                then,
                else_opt,
            } => todo!(),
            hax_frontend_exporter::ExprKind::Call {
                ty,
                fun,
                args,
                from_hir_call,
                fn_span,
            } => todo!(),
            hax_frontend_exporter::ExprKind::Deref { arg } => todo!(),
            hax_frontend_exporter::ExprKind::Binary { op, lhs, rhs } => todo!(),
            hax_frontend_exporter::ExprKind::LogicalOp { op, lhs, rhs } => todo!(),
            hax_frontend_exporter::ExprKind::Unary { op, arg } => todo!(),
            hax_frontend_exporter::ExprKind::Cast { source } => todo!(),
            hax_frontend_exporter::ExprKind::Use { source } => todo!(),
            hax_frontend_exporter::ExprKind::NeverToAny { source } => todo!(),
            hax_frontend_exporter::ExprKind::PointerCoercion { cast, source } => todo!(),
            hax_frontend_exporter::ExprKind::Loop { body } => todo!(),
            hax_frontend_exporter::ExprKind::Match { scrutinee, arms } => todo!(),
            hax_frontend_exporter::ExprKind::Let { expr, pat } => todo!(),
            hax_frontend_exporter::ExprKind::Block { block } => {
                return block.expr.as_ref().unwrap().import();
            }
            hax_frontend_exporter::ExprKind::Assign { lhs, rhs } => todo!(),
            hax_frontend_exporter::ExprKind::AssignOp { op, lhs, rhs } => todo!(),
            hax_frontend_exporter::ExprKind::Field { field, lhs } => todo!(),
            hax_frontend_exporter::ExprKind::TupleField { field, lhs } => todo!(),
            hax_frontend_exporter::ExprKind::Index { lhs, index } => todo!(),
            hax_frontend_exporter::ExprKind::VarRef { id } => todo!(),
            hax_frontend_exporter::ExprKind::ConstRef { id } => todo!(),
            hax_frontend_exporter::ExprKind::GlobalName { item, constructor } => todo!(),
            hax_frontend_exporter::ExprKind::UpvarRef {
                closure_def_id,
                var_hir_id,
            } => todo!(),
            hax_frontend_exporter::ExprKind::Borrow { borrow_kind, arg } => todo!(),
            hax_frontend_exporter::ExprKind::RawBorrow { mutability, arg } => todo!(),
            hax_frontend_exporter::ExprKind::Break { label, value } => todo!(),
            hax_frontend_exporter::ExprKind::Continue { label } => todo!(),
            hax_frontend_exporter::ExprKind::Return { value } => todo!(),
            hax_frontend_exporter::ExprKind::ConstBlock(item_ref) => todo!(),
            hax_frontend_exporter::ExprKind::Repeat { value, count } => todo!(),
            hax_frontend_exporter::ExprKind::Array { fields } => todo!(),
            hax_frontend_exporter::ExprKind::Tuple { fields } => ast::ExprKind::Construct {
                constructor: ast::GlobalId::unit_constructor(),
                is_record: false,
                is_struct: true,
                fields: Vec::new(),
                base: None,
            },
            hax_frontend_exporter::ExprKind::Adt(adt_expr) => todo!(),
            hax_frontend_exporter::ExprKind::PlaceTypeAscription { source, user_ty } => todo!(),
            hax_frontend_exporter::ExprKind::ValueTypeAscription { source, user_ty } => todo!(),
            hax_frontend_exporter::ExprKind::Closure {
                params,
                body,
                upvars,
                movability,
            } => todo!(),
            hax_frontend_exporter::ExprKind::Literal { lit, neg } => todo!(),
            hax_frontend_exporter::ExprKind::ZstLiteral { user_ty } => todo!(),
            hax_frontend_exporter::ExprKind::NamedConst { item, user_ty } => todo!(),
            hax_frontend_exporter::ExprKind::ConstParam { param, def_id } => todo!(),
            hax_frontend_exporter::ExprKind::StaticRef {
                alloc_id,
                ty,
                def_id,
            } => todo!(),
            hax_frontend_exporter::ExprKind::Yield { value } => todo!(),
            hax_frontend_exporter::ExprKind::Todo(_) => todo!(),
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
        // TODO #1763 missing metadata for trait item
        let meta = ast::Metadata {
            span: ast::span::Span::dummy(),
            attributes: Vec::new(),
        };
        // TODO #17663 missing generics/param_env for trait items
        let generics = ast::Generics {
            params: Vec::new(),
            constraints: Vec::new(),
        };
        let kind = match &self.kind {
            // TODO #1763 Missing type for Fn and Const. Bounds for Ty?
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

impl Import<ast::ImplItem> for frontend::ImplAssocItem {
    fn import(&self) -> ast::ImplItem {
        let kind = match &self.value {
            frontend::ImplAssocItemValue::Provided {
                def_id,
                is_override,
            } => todo!(),
            frontend::ImplAssocItemValue::DefaultedTy { ty } => todo!(),
            frontend::ImplAssocItemValue::DefaultedFn => todo!(),
            frontend::ImplAssocItemValue::DefaultedConst => todo!(),
        };
        ast::ImplItem {
            // TODO #1763 Missing metadata on ImplAssocItem
            meta: todo!(),
            // TODO #1763 Missing generics on ImplAssocItem
            generics: todo!(),
            kind,
            ident: self.def_id().import(),
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
    todo!() // TODO Implement to evaluate what is needed in #1763
}

impl Import<Vec<ast::Item>> for frontend::FullDef<frontend::Expr> {
    fn import(&self) -> Vec<ast::Item> {
        let Self {
            this,
            span,
            source_span,
            source_text,
            attributes,
            visibility,
            lang_item,
            diagnostic_item,
            kind,
        } = self;
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
                        frontend::AdtKind::Union => todo!(),
                        frontend::AdtKind::Enum => false,
                    },
                }
            }
            frontend::FullDefKind::TyAlias { param_env, ty } => todo!(),
            frontend::FullDefKind::ForeignTy => todo!(),
            frontend::FullDefKind::AssocTy {
                param_env,
                implied_predicates,
                associated_item,
                value,
            } => todo!(),
            frontend::FullDefKind::OpaqueTy => todo!(),
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
            } => todo!(),
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
                    panic!(
                        "Self should always be the first generic argument of a trait application."
                    )
                };
                ast::ItemKind::Impl {
                    generics,
                    self_ty: self_ty.clone(),
                    of_trait,
                    items: items.iter().map(frontend::ImplAssocItem::import).collect(),
                    // TODO #1763 clauses and safety missing in implied_impl_exprs
                    parent_bounds: todo!(),
                    safety: todo!(),
                }
            }
            frontend::FullDefKind::InherentImpl {
                param_env,
                ty,
                items,
            } => todo!(),
            frontend::FullDefKind::Fn {
                param_env,
                sig,
                body,
                ..
            } => {
                ast::ItemKind::Fn {
                    name: ident,
                    generics: param_env.import(),
                    body: body
                        .as_ref()
                        .expect("Functions without body are not supported")
                        .import(),
                    params: Vec::new(), // TODO(missing) #1763 Change TyFnSignature to add parameter binders
                    safety: sig.value.safety.import(),
                }
            }
            frontend::FullDefKind::AssocFn {
                param_env,
                associated_item,
                inline,
                is_const,
                sig,
                body,
            } => todo!(),
            frontend::FullDefKind::Closure {
                args,
                is_const,
                fn_once_impl,
                fn_mut_impl,
                fn_impl,
                once_shim,
                drop_glue,
                drop_impl,
            } => todo!(),
            frontend::FullDefKind::Const {
                param_env,
                ty,
                kind,
                body,
            } => todo!(),
            frontend::FullDefKind::AssocConst {
                param_env,
                associated_item,
                ty,
                body,
            } => todo!(),
            frontend::FullDefKind::Static {
                param_env,
                safety,
                mutability,
                nested,
                ty,
                body,
            } => todo!(),
            frontend::FullDefKind::ExternCrate => todo!(),
            frontend::FullDefKind::Use => todo!(),
            frontend::FullDefKind::Mod { items } => todo!(),
            frontend::FullDefKind::ForeignMod { items } => todo!(),
            frontend::FullDefKind::TyParam => todo!(),
            frontend::FullDefKind::ConstParam => todo!(),
            frontend::FullDefKind::LifetimeParam => todo!(),
            frontend::FullDefKind::Variant => todo!(),
            frontend::FullDefKind::Ctor {
                adt_def_id,
                ctor_of,
                variant_id,
                fields,
                output_ty,
            } => todo!(),
            frontend::FullDefKind::Field => todo!(),
            frontend::FullDefKind::Macro(macro_kind) => todo!(),
            frontend::FullDefKind::GlobalAsm => todo!(),
            frontend::FullDefKind::SyntheticCoroutineBody => todo!(),
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
}
