use crate::ast::identifiers::GlobalId;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Phase to extract definitions outside trait impls
///
/// This phase hoists the definitions of associated functions (and constants),
/// to handle dependencies, recursion and mutual recursion between them.
#[derive(Default, Debug)]
pub struct HoistAssociatedFns;

/// Visitor to rewrite calls to the hoisted methods
#[setup_error_handling_struct]
struct HoistAssociatedFnsVisitor<'a> {
    /// The trait goal corresponding to the impl being treated
    of_trait: &'a TraitGoal,
    /// The name of the impl
    impl_name: GlobalId,
}

impl<'a> HoistAssociatedFnsVisitor<'a> {
    fn new(of_trait: &'a TraitGoal, impl_name: GlobalId) -> Self {
        Self {
            of_trait,
            impl_name,
            error_handling_state: wrappers::ErrorHandlingState::default(),
        }
    }
}

fn context() -> Context {
    Context::Phase(stringify!(HoistAssociatedFns).to_string())
}

impl<'a> VisitorWithContext for HoistAssociatedFnsVisitor<'a> {
    fn context(&self) -> Context {
        context()
    }
}

fn hoisted_name(assoc_item_name: GlobalId) -> GlobalId {
    assoc_item_name.map_last(&(|s: &mut String| s.push_str("_hoisted")))
}

impl<'a> AstVisitorMut for HoistAssociatedFnsVisitor<'a> {
    setup_error_handling_impl!();

    fn visit_expr_kind(&mut self, x: &mut ExprKind) {
        self.visit_inner(x);
        if let ExprKind::App {
            head,
            generic_args,
            trait_,
            ..
        } = x
            && let ExprKind::GlobalId(name) = head.kind_mut()
            && trait_.as_ref().is_some_and(|t| self.of_trait == &t.0.goal)
        {
            let mut new_generic_args = self.of_trait.args[1..].to_vec();
            new_generic_args.append(generic_args);
            *generic_args = new_generic_args;
            *trait_ = None;
            *name =
                hoisted_name(name.rename_method_as_hoisted(self.of_trait.trait_, self.impl_name));
        }
    }
}

impl Phase for HoistAssociatedFns {
    fn apply(&self, items: &mut Vec<Item>) {
        let mut new_items = Vec::new();
        for item in items.iter() {
            let mut new_item = item.clone();
            match new_item.kind_mut() {
                ItemKind::Impl {
                    generics: impl_generics,
                    of_trait,
                    items,
                    ..
                } => {
                    for trait_item in items {
                        if let ImplItem {
                            meta,
                            generics,
                            kind: ImplItemKind::Fn { body, params },
                            ident,
                        } = trait_item
                            && !ident.is_postcondition()
                            && !ident.is_precondition()
                        // We ignore specs as they are not supported by the Lean backend for now
                        {
                            let fn_name = hoisted_name(ident.clone());
                            let full_generics = impl_generics.clone().concat(generics.clone());
                            let mut fn_body = body.clone();
                            HoistAssociatedFnsVisitor::new(of_trait, item.ident)
                                .visit_expr(&mut fn_body);
                            let used_params: Vec<Param> = params
                                .iter()
                                .filter(|p| !matches!(p.pat.kind(), PatKind::Wild))
                                .cloned()
                                .collect();

                            let generic_args = full_generics
                                .params
                                .iter()
                                .map(|p| match p.kind() {
                                    GenericParamKind::Lifetime => GenericValue::Lifetime,
                                    GenericParamKind::Type => {
                                        GenericValue::Ty(TyKind::Param(p.ident.clone()).promote())
                                    }
                                    GenericParamKind::Const { ty } => GenericValue::Expr(
                                        ExprKind::LocalId(p.ident.clone())
                                            .promote(ty.clone(), p.span()),
                                    ),
                                })
                                .collect();
                            let args = used_params.iter().map(|p| match p.pat.kind() {
                                PatKind::Binding { var, .. } =>
                                ExprKind::LocalId(var.clone()),
                                _ => ExprKind::Error(
                                    ErrorNode::assertion_failure(p.pat.clone(), context(),
                                    "Non-trivial patterns are not supported for associated functions hoisting.")
                                ),
                            }.promote(p.ty.clone(), p.pat.span())).collect();
                            let fn_item = Item {
                                ident: fn_name,
                                kind: ItemKind::Fn {
                                    name: fn_name,
                                    generics: full_generics.clone(),
                                    body: fn_body,
                                    params: used_params,
                                    safety: SafetyKind::Safe,
                                },
                                meta: meta.clone(),
                            };
                            new_items.push(fn_item);
                            *body.kind_mut() = ExprKind::standalone_fn_app(
                                fn_name,
                                generic_args,
                                args,
                                body.ty.clone(),
                                body.span(),
                            )
                        }
                    }
                }
                _ => (),
            }
            new_items.push(new_item)
        }
        *items = new_items;
    }
}
