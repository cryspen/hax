//! `#[hax_lib::pv_inline]` resugaring.
//!
//! Walks the AST in two passes:
//!
//!  1. **Collect** every item tagged with [`AttrPayload::PVInline`] into a
//!     shared map keyed by its `GlobalId`, recording its parameter list
//!     and body. Inherent / trait impl methods are picked up too.
//!  2. **Apply**: every `ExprKind::App` whose head resolves to one of the
//!     collected `GlobalId`s is replaced by a fresh, hygienically renamed
//!     copy of the body with each formal parameter substituted by the
//!     corresponding actual argument. If an actual argument is a
//!     [`ExprKind::Closure`], every call of the corresponding formal in
//!     the body is β-reduced into the closure's body.
//!
//! Finally, the inlined items are marked
//! `AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true })`
//! so `drop_skip_late_items` in `backends.rs` removes them from the
//! emitted file.
//!
//! Designed for higher-order helpers (`Option::map`, `iter::fold`, …)
//! which would otherwise extract as opaque function symbols when the
//! ProVerif printer has nothing to say about them.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use hax_lib_macros_types::{AttrPayload, ItemStatus};

use crate::ast::identifiers::{GlobalId, LocalId};
use crate::ast::visitors::*;
use crate::ast::*;
use crate::printer::Resugaring;
use crate::symbol::Symbol;

/// Bound on the substitution fixpoint, to keep the resugaring total.
const MAX_INLINE_DEPTH: usize = 100;

/// Shared state between [`CollectPVInline`] and [`ApplyPVInline`].
#[derive(Default)]
struct Shared {
    /// Map of inlinable function: `GlobalId → (params, body)`.
    inlinable: HashMap<GlobalId, (Vec<Param>, Expr)>,
}

/// Build the two-phase resugaring pipeline (collect + apply) sharing a
/// single mutable state. Both phases must be registered together for
/// inlining to work.
pub fn pv_inline_resugarings() -> Vec<Box<dyn Resugaring>> {
    let shared = Rc::new(RefCell::new(Shared::default()));
    vec![
        Box::new(CollectPVInline {
            shared: shared.clone(),
        }),
        Box::new(ApplyPVInline {
            shared,
            next_fresh: 0,
        }),
    ]
}

/// The path under which the `pv_inline` tool attribute lands on items
/// after the proc-macro emits
/// `#[cfg_attr(hax_compilation, _hax::pv_inline)]`. We use a tool
/// attribute rather than an `AttrPayload` variant so the OCaml engine
/// shuttles it through unparsed.
const PV_INLINE_PATH: &str = "_hax::pv_inline";

fn meta_has_pv_inline(meta: &Metadata) -> bool {
    meta.attributes.iter().any(|a| matches!(
        &a.kind,
        AttributeKind::Tool { path, .. } if path == PV_INLINE_PATH
    ))
}

fn meta_is_opaque(meta: &Metadata) -> bool {
    meta.hax_attributes()
        .any(|a| matches!(a, AttrPayload::Erased))
}

/// Returns true if any of `params` has an arrow (closure / fn) type — the
/// signature of a higher-order function. ProVerif has no functions-as-
/// values, so any such call site must be inlined to make sense.
fn params_contain_arrow(params: &[Param]) -> bool {
    params
        .iter()
        .any(|p| matches!(p.ty.kind(), TyKind::Arrow { .. }))
}

/// Walks an expression to detect a reference to `target` — used to avoid
/// inlining a recursive HOF (which would loop the substitution fixpoint).
struct SelfRef {
    target: GlobalId,
    found: bool,
}

impl AstVisitor for SelfRef {
    fn enter_expr_kind(&mut self, x: &ExprKind) {
        if let ExprKind::GlobalId(id) = x
            && *id == self.target
        {
            self.found = true;
        }
    }
}

fn body_references(body: &Expr, target: GlobalId) -> bool {
    let mut v = SelfRef {
        target,
        found: false,
    };
    v.visit_expr(body);
    v.found
}

// === Pass 1: collect inlinable items =======================================

struct CollectPVInline {
    shared: Rc<RefCell<Shared>>,
}

impl CollectPVInline {
    /// Decide whether `params` + `body` (identified as `name`) should be
    /// inlinable. Three sources of opt-in, in priority order:
    ///  1. Explicit `#[hax_lib::pv_inline]` tool attribute on the item.
    ///  2. Auto-inferred: the item is a higher-order function (some
    ///     `Param` has a `TyKind::Arrow` type). ProVerif has no
    ///     functions-as-values, so HOFs only make sense if inlined at
    ///     every call site.
    /// We *skip* items tagged `#[hax_lib::opaque]` and items whose body
    /// references themselves (recursive — would loop the fixpoint).
    fn should_inline(
        &self,
        meta: &Metadata,
        params: &[Param],
        body: &Expr,
        name: GlobalId,
    ) -> bool {
        if meta_is_opaque(meta) {
            return false;
        }
        let opt_in = meta_has_pv_inline(meta) || params_contain_arrow(params);
        if !opt_in {
            return false;
        }
        if body_references(body, name) {
            // Recursive HOF — leave it as an opaque call.
            return false;
        }
        true
    }
}

impl AstVisitorMut for CollectPVInline {
    fn enter_item(&mut self, item: &mut Item) {
        if let ItemKind::Fn {
            name, body, params, ..
        } = &item.kind
            && self.should_inline(&item.meta, params, body, *name)
        {
            self.shared
                .borrow_mut()
                .inlinable
                .insert(*name, (params.clone(), body.clone()));
        }
    }

    fn enter_impl_item(&mut self, impl_item: &mut ImplItem) {
        if let ImplItemKind::Fn { body, params } = &impl_item.kind
            && self.should_inline(&impl_item.meta, params, body, impl_item.ident)
        {
            self.shared
                .borrow_mut()
                .inlinable
                .insert(impl_item.ident, (params.clone(), body.clone()));
        }
    }
}

impl Resugaring for CollectPVInline {
    fn name(&self) -> String {
        "pv-inline-collect".to_string()
    }
}

// === Pass 2: apply inlining and mark items late-skip =======================

struct ApplyPVInline {
    shared: Rc<RefCell<Shared>>,
    /// Per-resugaring counter used to gensym local names in inlined bodies.
    next_fresh: usize,
}

impl ApplyPVInline {
    /// Mint a fresh local id by prefixing the existing name with a counter.
    fn fresh_id(&mut self, base: &LocalId) -> LocalId {
        self.next_fresh += 1;
        LocalId(Symbol::new(&format!("inl{}__{}", self.next_fresh, base.0)))
    }

    /// Inline a single App if its head is a known inlinable.
    /// Returns the rewritten expression, or `None` to keep the App as-is.
    fn try_inline_app(&mut self, expr: &Expr) -> Option<Expr> {
        let ExprKind::App { head, args, .. } = &*expr.kind else {
            return None;
        };
        let ExprKind::GlobalId(g) = &*head.kind else {
            return None;
        };
        let (params, body) = self.shared.borrow().inlinable.get(g).cloned()?;
        if params.len() != args.len() {
            // Arity mismatch — bail out and leave the call opaque.
            return None;
        }
        // Build the param-name → arg map.
        let mut env: HashMap<LocalId, Expr> = HashMap::new();
        let mut rename: HashMap<LocalId, LocalId> = HashMap::new();
        for (param, arg) in params.iter().zip(args.iter()) {
            if let Some(id) = param_local_id(param) {
                env.insert(id, arg.clone());
            }
        }
        let mut body = body;
        // α-rename binders in `body` so this inlining gets fresh names.
        self.alpha_rename(&mut body, &mut rename);
        // Substitute and β-reduce closures.
        self.subst(&mut body, &env);
        Some(body)
    }

    /// Replace every `LocalId(k → fresh_v)` in the body's *binders* and
    /// keep the same renaming under usage sites. We do this first so the
    /// substitution that follows doesn't capture variables that happen to
    /// share a name with a binder introduced inside the body.
    fn alpha_rename(&mut self, expr: &mut Expr, rename: &mut HashMap<LocalId, LocalId>) {
        match &mut *expr.kind {
            ExprKind::Let { lhs, rhs, body } => {
                self.alpha_rename(rhs, rename);
                self.alpha_rename_pat(lhs, rename);
                self.alpha_rename(body, rename);
            }
            ExprKind::LocalId(id) => {
                if let Some(new) = rename.get(id) {
                    *id = new.clone();
                }
            }
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                for p in params.iter_mut() {
                    self.alpha_rename_pat(p, rename);
                }
                for c in captures.iter_mut() {
                    self.alpha_rename(c, rename);
                }
                self.alpha_rename(body, rename);
            }
            ExprKind::Match { scrutinee, arms } => {
                self.alpha_rename(scrutinee, rename);
                for arm in arms.iter_mut() {
                    self.alpha_rename_pat(&mut arm.pat, rename);
                    self.alpha_rename(&mut arm.body, rename);
                }
            }
            ExprKind::App { head, args, .. } => {
                self.alpha_rename(head, rename);
                for a in args.iter_mut() {
                    self.alpha_rename(a, rename);
                }
            }
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.alpha_rename(condition, rename);
                self.alpha_rename(then, rename);
                if let Some(e) = else_ {
                    self.alpha_rename(e, rename);
                }
            }
            ExprKind::Construct { fields, base, .. } => {
                for (_, v) in fields.iter_mut() {
                    self.alpha_rename(v, rename);
                }
                if let Some(b) = base {
                    self.alpha_rename(b, rename);
                }
            }
            ExprKind::Ascription { e, .. } => self.alpha_rename(e, rename),
            ExprKind::Array(es) => {
                for e in es {
                    self.alpha_rename(e, rename);
                }
            }
            ExprKind::Return { value } => self.alpha_rename(value, rename),
            // Nothing to rename in leaves.
            _ => {}
        }
    }

    fn alpha_rename_pat(&mut self, pat: &mut Pat, rename: &mut HashMap<LocalId, LocalId>) {
        match &mut *pat.kind {
            PatKind::Binding { var, sub_pat, .. } => {
                let new = self.fresh_id(var);
                rename.insert(var.clone(), new.clone());
                *var = new;
                if let Some(sp) = sub_pat {
                    self.alpha_rename_pat(sp, rename);
                }
            }
            PatKind::Construct { fields, .. } => {
                for (_, p) in fields.iter_mut() {
                    self.alpha_rename_pat(p, rename);
                }
            }
            PatKind::Ascription { pat, .. } => self.alpha_rename_pat(pat, rename),
            PatKind::Or { sub_pats } => {
                for p in sub_pats {
                    self.alpha_rename_pat(p, rename);
                }
            }
            PatKind::Array { args } => {
                for p in args.iter_mut() {
                    self.alpha_rename_pat(p, rename);
                }
            }
            PatKind::Deref { sub_pat, .. } => self.alpha_rename_pat(sub_pat, rename),
            _ => {}
        }
    }

    /// Substitute every reference to `env`'s keys with the corresponding
    /// value, β-reducing whenever a substituted closure is in head
    /// position of an `App`.
    fn subst(&mut self, expr: &mut Expr, env: &HashMap<LocalId, Expr>) {
        match &mut *expr.kind {
            ExprKind::LocalId(id) => {
                if let Some(rep) = env.get(id) {
                    *expr = rep.clone();
                }
            }
            ExprKind::App { head, args, .. } => {
                // First substitute through args.
                for a in args.iter_mut() {
                    self.subst(a, env);
                }
                // If the head is `LocalId(p)` and `env[p]` is a closure,
                // β-reduce in place: drop the closure wrapper and inline
                // its body with params bound to `args`.
                if let ExprKind::LocalId(id) = &*head.kind
                    && let Some(rep) = env.get(id)
                    && let ExprKind::Closure {
                        params,
                        body,
                        captures: _,
                    } = &*rep.kind
                    && params.len() == args.len()
                {
                    let mut cl_env: HashMap<LocalId, Expr> = HashMap::new();
                    let mut cl_rename: HashMap<LocalId, LocalId> = HashMap::new();
                    let mut body = body.clone();
                    // Hygiene: rename binders inside the closure body
                    // before we substitute its params away.
                    let mut clp = params.clone();
                    for p in clp.iter_mut() {
                        self.alpha_rename_pat(p, &mut cl_rename);
                    }
                    self.alpha_rename(&mut body, &mut cl_rename);
                    for (cp, ca) in clp.iter().zip(args.iter()) {
                        if let Some(local) = pat_local_id(cp) {
                            cl_env.insert(local, ca.clone());
                        }
                    }
                    self.subst(&mut body, &cl_env);
                    *expr = body;
                    return;
                }
                self.subst(head, env);
            }
            ExprKind::Let { lhs: _, rhs, body } => {
                self.subst(rhs, env);
                self.subst(body, env);
            }
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.subst(condition, env);
                self.subst(then, env);
                if let Some(e) = else_ {
                    self.subst(e, env);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.subst(scrutinee, env);
                for arm in arms.iter_mut() {
                    self.subst(&mut arm.body, env);
                }
            }
            ExprKind::Construct { fields, base, .. } => {
                for (_, v) in fields.iter_mut() {
                    self.subst(v, env);
                }
                if let Some(b) = base {
                    self.subst(b, env);
                }
            }
            ExprKind::Closure {
                params: _,
                body,
                captures,
            } => {
                for c in captures.iter_mut() {
                    self.subst(c, env);
                }
                self.subst(body, env);
            }
            ExprKind::Ascription { e, .. } => self.subst(e, env),
            ExprKind::Array(es) => {
                for e in es {
                    self.subst(e, env);
                }
            }
            ExprKind::Return { value } => self.subst(value, env),
            _ => {}
        }
    }
}

fn param_local_id(p: &Param) -> Option<LocalId> {
    pat_local_id(&p.pat)
}

fn pat_local_id(p: &Pat) -> Option<LocalId> {
    match &*p.kind {
        PatKind::Binding { var, .. } => Some(var.clone()),
        PatKind::Ascription { pat, .. } => pat_local_id(pat),
        _ => None,
    }
}

impl AstVisitorMut for ApplyPVInline {
    fn enter_item(&mut self, item: &mut Item) {
        // Mark inlinable items as late-skip so the printer drops them.
        // We consult the shared map (populated by CollectPVInline) rather
        // than re-checking the attribute, so the auto-inferred HOFs are
        // dropped too.
        let is_inlinable = if let ItemKind::Fn { name, .. } = &item.kind {
            self.shared.borrow().inlinable.contains_key(name)
        } else {
            false
        };
        if is_inlinable {
            item.meta.attributes.push(Attribute {
                kind: AttributeKind::Hax(AttrPayload::ItemStatus(ItemStatus::Included {
                    late_skip: true,
                })),
                span: item.meta.span.clone(),
            });
        }
    }

    fn enter_impl_item(&mut self, impl_item: &mut ImplItem) {
        if self.shared.borrow().inlinable.contains_key(&impl_item.ident) {
            impl_item.meta.attributes.push(Attribute {
                kind: AttributeKind::Hax(AttrPayload::ItemStatus(ItemStatus::Included {
                    late_skip: true,
                })),
                span: impl_item.meta.span.clone(),
            });
        }
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        // Iterate to fixpoint: an inlined body may itself call another
        // inlinable, so we re-check until no more rewrites happen (or
        // until we hit the recursion bound).
        for _ in 0..MAX_INLINE_DEPTH {
            match self.try_inline_app(expr) {
                Some(new) => *expr = new,
                None => break,
            }
        }
    }
}

impl Resugaring for ApplyPVInline {
    fn name(&self) -> String {
        "pv-inline-apply".to_string()
    }
}
