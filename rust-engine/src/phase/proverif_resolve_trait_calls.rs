//! ProVerif-backend phase: resolve trait-method calls to concrete impl methods.
//!
//! ProVerif is first-order and has no traits: every call must name a concrete
//! function. The other backends (F\*, Lean) keep trait methods abstract and rely
//! on the target language's typeclass mechanism, so the engine never
//! monomorphizes a user trait call. For ProVerif that leaves call sites such as
//! `self.sk.add_prefix(p)` (where `self.sk: Bytes`) rendered as the *trait*
//! method name `Prefix__add_prefix`, which the auto-decl pass then turns into an
//! opaque (and unsound) function — even though the concrete impl method
//! (`Impl_1__add_prefix`) was extracted right next to it.
//!
//! Inherent methods (`Vec::push`, `slice::iter`, …) carry their concrete id as
//! the `App` head already, so they are unaffected; only *trait* method calls
//! reach the printer with `trait_: Some(..)` and a head naming the trait method.
//!
//! This phase indexes every `impl` block by `(trait id, Self-type head, method
//! name)` and rewrites each such `App` head to the matching concrete impl
//! method, using the call's resolved trait goal (`ImplExpr::goal`) to recover
//! the concrete Self type. Calls whose Self type is a generic parameter
//! (`LocalBound`) have no concrete head and are left untouched, as are std
//! traits with no user impl in scope (e.g. `PartialEq::eq`, modeled in
//! `primitives.pvl`).
//!
//! Set `HAX_PV_DEBUG_TRAITS=1` to log every trait-call resolution attempt.

use std::collections::HashMap;

use crate::ast::identifiers::GlobalId;
use crate::ast::identifiers::global_id::view::PathSegmentPayload;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Phase resolving user trait-method calls to their concrete impl methods.
#[derive(Default, Debug)]
pub struct ProverifResolveTraitCalls;

/// Resolution key: `(trait id, Self-type head key, method name)`.
type Key = (GlobalId, String, String);

#[setup_error_handling_struct]
#[derive(Default)]
struct ResolveTraitCallsVisitor {
    /// `(trait, Self-type head, method) -> concrete impl method id`.
    resolution: HashMap<Key, GlobalId>,
}

impl VisitorWithContext for ResolveTraitCallsVisitor {
    fn context(&self) -> Context {
        Context::Phase(stringify!(ProverifResolveTraitCalls).to_string())
    }
}

/// A coarse key for the *head* of a type — enough to tell apart the distinct
/// `Self` types a trait is implemented for. Generic-parameter Self types
/// (`Param`) deliberately return `None`, so a call resolved through a generic
/// bound never matches a concrete impl. References are peeled.
fn ty_head_key(ty: &Ty) -> Option<String> {
    let Ty(kind) = ty;
    match &**kind {
        TyKind::App { head, .. } => Some(head.to_debug_string()),
        TyKind::Ref { inner, .. } => ty_head_key(inner),
        TyKind::Slice(_) => Some("$slice".to_string()),
        TyKind::Array { .. } => Some("$array".to_string()),
        TyKind::Primitive(p) => Some(format!("$prim:{p:?}")),
        _ => None,
    }
}

/// The final path segment's name (the method name), if it is a named segment.
fn method_name(g: GlobalId) -> Option<String> {
    match g.view().last().payload() {
        PathSegmentPayload::Named(s) => Some(s.to_string()),
        PathSegmentPayload::Unnamed(_) => None,
    }
}

fn debug_enabled() -> bool {
    std::env::var_os("HAX_PV_DEBUG_TRAITS").is_some()
}

impl AstVisitorMut for ResolveTraitCallsVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        self.visit_inner(expr);

        // Compute the concrete method id (if any), ending the borrow on
        // `expr.kind` before mutating.
        let resolved: Option<GlobalId> = {
            let ExprKind::App {
                head,
                trait_: Some((impl_expr, _)),
                ..
            } = &*expr.kind
            else {
                return;
            };
            let ExprKind::GlobalId(g) = &*head.kind else {
                return;
            };
            let Some(mname) = method_name(*g) else {
                return;
            };
            let goal = &impl_expr.goal;
            let self_key = match goal.args.first() {
                Some(GenericValue::Ty(self_ty)) => ty_head_key(self_ty),
                _ => None,
            };
            let hit = self_key.as_ref().and_then(|sk| {
                self.resolution
                    .get(&(goal.trait_, sk.clone(), mname.clone()))
                    .copied()
            });
            if debug_enabled() {
                eprintln!(
                    "[pv-traits] call {} trait={} self_head={:?} method={} -> {:?}",
                    g.to_debug_string(),
                    goal.trait_.to_debug_string(),
                    self_key,
                    mname,
                    hit.map(|h| h.to_debug_string()),
                );
            }
            hit
        };

        let Some(concrete) = resolved else {
            return;
        };
        if let ExprKind::App { head, .. } = &mut *expr.kind {
            let span = head.meta.span;
            let ty = head.ty.clone();
            *head = ExprKind::GlobalId(concrete).promote(ty, span);
        }
    }
}

impl Phase for ProverifResolveTraitCalls {
    fn apply(&self, items: &mut Vec<Item>) {
        // Index every impl block's methods by (trait, Self-type head, method).
        let mut resolution: HashMap<Key, GlobalId> = HashMap::new();
        for item in items.iter() {
            let ItemKind::Impl {
                self_ty,
                of_trait,
                items: impl_items,
                ..
            } = &item.kind
            else {
                continue;
            };
            let Some(self_key) = ty_head_key(self_ty) else {
                continue;
            };
            let trait_id = of_trait.trait_;
            for impl_item in impl_items {
                if !matches!(impl_item.kind, ImplItemKind::Fn { .. }) {
                    continue;
                }
                let Some(mname) = method_name(impl_item.ident) else {
                    continue;
                };
                resolution.insert((trait_id, self_key.clone(), mname), impl_item.ident);
            }
        }

        if debug_enabled() {
            eprintln!("[pv-traits] indexed {} impl methods", resolution.len());
            for (k, v) in &resolution {
                eprintln!("[pv-traits]   {k:?} -> {}", v.to_debug_string());
            }
        }

        ResolveTraitCallsVisitor {
            resolution,
            ..Default::default()
        }
        .visit(items)
    }
}
