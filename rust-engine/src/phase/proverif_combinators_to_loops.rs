//! ProVerif-backend phase: rewrite iterator-combinator calls into for-loops.
//!
//! The ProVerif printer cannot print closures (`[HAX0001] Closures not
//! supported`). Several common iterator combinators reach the printer as an
//! `App` whose head is a trait method (`Iterator::fold` / `Iterator::find` /
//! `Iterator::any`) applied to a `Closure` argument.
//!
//! This phase rewrites such calls into `ExprKind::Loop { kind: ForLoop, state:
//! Some(..), .. }` nodes whose functional shape the printer already knows how to
//! unroll to a fixed `LOOP_BOUND` depth via the opaque
//! `__iter_empty`/`__iter_head`/`__iter_tail` helpers (see
//! `backends/proverif.rs`). The closure parameters are reused directly as the
//! loop binders (no substitution needed): for `fold` the element pattern is the
//! `ForLoop` pattern and the accumulator pattern is the loop-state `body_pat`.
//!
//! core-models bodies aren't loaded for ProVerif (name-only rewrite), and only
//! `fold` has a referenceable `GlobalId` in the generated names, so the
//! combinators are matched by the `GlobalId`'s debug path string instead.

use crate::ast::identifiers::GlobalId;
use crate::ast::literals::Literal;
use crate::ast::span::Span;
use crate::ast::*;
use crate::ast::{diagnostics::*, visitors::*};
use crate::phase::Phase;

/// Phase that rewrites iterator combinators (`fold`/`find`/`any`) applied to a
/// closure into bounded `ForLoop` nodes that the ProVerif printer can unroll.
#[derive(Default, Debug)]
pub struct ProverifCombinatorsToLoops;

/// Stateless visitor.
#[setup_error_handling_struct]
#[derive(Default)]
struct ProverifCombinatorsToLoopsVisitor;

impl VisitorWithContext for ProverifCombinatorsToLoopsVisitor {
    fn context(&self) -> Context {
        Context::Phase(stringify!(ProverifCombinatorsToLoops).to_string())
    }
}

/// Which combinator a call site matched.
#[derive(Clone, Copy, Debug)]
enum Combinator {
    Fold,
    Find,
    Any,
    /// `Option::map(opt, |x| body)` — rewritten to a scalar `match`, not a loop.
    OptionMap,
    /// `Iterator::find_map(iter, |x| body)` where `body : Option<_>`.
    FindMap,
    /// `Iterator::collect(Iterator::map(iter, |x| body))` — rewritten to a
    /// cons-list-building `ForLoop`.
    MapCollect,
    /// `bool::then(cond, || body)` — rewritten to a scalar
    /// `if cond { Some(body) } else { None }`.
    BoolThen,
    /// `Iterator::for_each(iter, |x| body)` — rewritten to a no-accumulator
    /// (`state: None`) `ForLoop`.
    ForEach,
    /// `Iterator::filter_map(iter, |x| body)` where `body : Option<_>` —
    /// rewritten to a cons-list-building `ForLoop` keeping only the `Some`
    /// payloads.
    FilterMap,
}

/// Classify the head `GlobalId` of an `App` by its debug path string. Returns
/// `None` if it is not one of the combinators we rewrite.
fn classify(head: &Expr) -> Option<Combinator> {
    let ExprKind::GlobalId(g) = &*head.kind else {
        return None;
    };
    let path = g.to_debug_string();
    if path.ends_with("Iterator::fold") {
        Some(Combinator::Fold)
    } else if path.ends_with("Iterator::find") {
        Some(Combinator::Find)
    } else if path.ends_with("Iterator::any") {
        Some(Combinator::Any)
    } else if path.ends_with("Iterator::find_map") {
        Some(Combinator::FindMap)
    } else if path.ends_with("Iterator::for_each") {
        Some(Combinator::ForEach)
    } else if path.ends_with("Iterator::filter_map") {
        Some(Combinator::FilterMap)
    } else if path.ends_with("Iterator::collect") {
        Some(Combinator::MapCollect)
    } else if path.ends_with("bool::impl::then") || path.ends_with("bool::then") {
        Some(Combinator::BoolThen)
    } else if path.contains("option") && path.ends_with("::map") {
        Some(Combinator::OptionMap)
    } else {
        None
    }
}

/// Peel a single `Ascription` / `Borrow` layer wrapping `e`, if any. Used to
/// reach the inner `map` application underneath a `collect`'s argument.
fn peel_wrappers(e: &Expr) -> &Expr {
    let mut current = e;
    loop {
        match &*current.kind {
            ExprKind::Ascription { e, .. } => current = e,
            ExprKind::Borrow { inner, .. } => current = inner,
            _ => return current,
        }
    }
}

/// Extract the payload type `T` of an `Option<T>` type, if `ty` has that
/// shape. Used to type the `Some(y)` binder in the `filter_map` rewrite. Falls
/// back to the whole `Option<T>` type otherwise (the ProVerif printer models
/// every value as `bitstring`, so an imprecise binder type is still sound).
fn option_payload_ty(ty: &Ty) -> Ty {
    let Ty(b) = ty;
    if let TyKind::App { args, .. } = &**b {
        if let Some(GenericValue::Ty(inner)) = args.first() {
            return inner.clone();
        }
    }
    ty.clone()
}

/// Extract the bound `LocalId` of a binding pattern, if any (peeling a single
/// ascription layer). Used to materialize `Some(<element var>)` for `find`.
fn pat_binding(pat: &Pat) -> Option<LocalId> {
    match &*pat.kind {
        PatKind::Binding { var, .. } => Some(var.clone()),
        PatKind::Ascription { pat, .. } => pat_binding(pat),
        _ => None,
    }
}

impl ProverifCombinatorsToLoopsVisitor {
    /// Build the `ForLoop` node for a `fold(iter, init, |acc, x| body)`.
    /// `args ≈ [iter, init, closure]`.
    fn rewrite_fold(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, init, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [acc_pat, elem_pat] = &params[..] else {
            return None;
        };
        let _ = (app_ty, span);
        Some(ExprKind::Loop {
            body: body.clone(),
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: init.clone(),
                body_pat: acc_pat.clone(),
            }),
            control_flow: None,
            label: None,
        })
    }

    /// Build the `ForLoop` node for a `find(iter, |x| pred)`.
    /// `args ≈ [iter, closure]`. The loop folds an `Option`: once it is `Some`,
    /// keep it; otherwise test the predicate on the current element and set it
    /// to `Some(x)` if it holds.
    fn rewrite_find(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };
        // The result of `find` is `Option<T>`: this is the App's type, and also
        // the loop-accumulator type.
        let option_ty = app_ty.clone();
        let elem_var = pat_binding(elem_pat)?;
        let elem_ty = elem_pat.ty.clone();

        // Constructors for `Option` and the `Some` payload field.
        let some_ctor = crate::names::core::option::Option::Some::Constructor;
        let none_ctor = crate::names::core::option::Option::None::Constructor;
        let some_field = crate::names::core::option::Option::Some::_0;

        // The accumulator binder threaded by the loop state.
        let acc_id: LocalId = "__find_acc".into();
        let acc_pat = PatKind::var_pat(acc_id.clone()).promote(option_ty.clone(), span);
        let acc_expr =
            ExprKind::LocalId(acc_id.clone()).promote(option_ty.clone(), span);

        // `None`
        let none_expr = ExprKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
            base: None,
        }
        .promote(option_ty.clone(), span);

        // `Some(<element var>)`
        let some_expr = ExprKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(
                some_field,
                ExprKind::LocalId(elem_var).promote(elem_ty, span),
            )],
            base: None,
        }
        .promote(option_ty.clone(), span);

        // `if <pred> { Some(x) } else { None }`
        let if_expr = ExprKind::If {
            condition: body.clone(),
            then: some_expr,
            else_: Some(none_expr),
        }
        .promote(option_ty.clone(), span);

        // Arm `Some(_) => __find_acc`
        let some_wild_pat = PatKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(
                some_field,
                PatKind::Wild.promote(option_ty.clone(), span),
            )],
        }
        .promote(option_ty.clone(), span);
        let some_arm = Arm::non_guarded(some_wild_pat, acc_expr.clone(), span);

        // Arm `None => if <pred> ...`
        let none_pat = PatKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
        }
        .promote(option_ty.clone(), span);
        let none_arm = Arm::non_guarded(none_pat, if_expr, span);

        // `match __find_acc { Some(_) => __find_acc, None => if ... }`
        let match_body = ExprKind::Match {
            scrutinee: acc_expr,
            arms: vec![some_arm, none_arm],
        }
        .promote(option_ty.clone(), span);

        Some(ExprKind::Loop {
            body: match_body,
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: none_expr_for_init(none_ctor, option_ty, span),
                body_pat: acc_pat,
            }),
            control_flow: None,
            label: None,
        })
    }

    /// Build the `ForLoop` node for an `any(iter, |x| pred)`.
    /// `args ≈ [iter, closure]`. Folds a boolean accumulator with
    /// `logical_op_or(acc, pred)`, starting from `false`.
    fn rewrite_any(span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };

        let bool_ty = Ty::bool();
        let acc_id: LocalId = "__any_acc".into();
        let acc_pat = PatKind::var_pat(acc_id.clone()).promote(bool_ty.clone(), span);
        let acc_expr = ExprKind::LocalId(acc_id).promote(bool_ty.clone(), span);

        let false_expr =
            ExprKind::Literal(Literal::Bool(false)).promote(bool_ty.clone(), span);

        // `logical_op_or(__any_acc, <pred>)`
        let or_body = Expr::standalone_fn_app(
            crate::names::rust_primitives::hax::logical_op_or,
            vec![],
            vec![acc_expr, body.clone()],
            bool_ty.clone(),
            span,
        );

        Some(ExprKind::Loop {
            body: or_body,
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: false_expr,
                body_pat: acc_pat,
            }),
            control_flow: None,
            label: None,
        })
    }

    /// Build the scalar `match` for an `Option::map(opt, |x| body)`.
    /// `args ≈ [opt, closure]`. Result is
    /// `match opt { Some(x) => Some(<body>), None => None }`, reusing the
    /// closure's parameter as the `Some` binder so `body`'s references to `x`
    /// stay valid (no substitution needed).
    fn rewrite_option_map(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [opt, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };
        let elem_var = pat_binding(elem_pat)?;
        let elem_ty = elem_pat.ty.clone();

        // The App's type is `Option<U>` (the mapped result type); the scrutinee
        // type is `Option<T>`.
        let out_option_ty = app_ty.clone();
        let in_option_ty = opt.ty.clone();

        let some_ctor = crate::names::core::option::Option::Some::Constructor;
        let none_ctor = crate::names::core::option::Option::None::Constructor;
        let some_field = crate::names::core::option::Option::Some::_0;

        // Arm `Some(x) => Some(<body>)` — bind the element with the closure's
        // own binder so the (unsubstituted) body sees `x`.
        let some_pat = PatKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(
                some_field,
                PatKind::var_pat(elem_var).promote(elem_ty, span),
            )],
        }
        .promote(in_option_ty.clone(), span);
        let some_result = ExprKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(some_field, body.clone())],
            base: None,
        }
        .promote(out_option_ty.clone(), span);
        let some_arm = Arm::non_guarded(some_pat, some_result, span);

        // Arm `None => None`
        let none_pat = PatKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
        }
        .promote(in_option_ty, span);
        let none_result = ExprKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
            base: None,
        }
        .promote(out_option_ty, span);
        let none_arm = Arm::non_guarded(none_pat, none_result, span);

        Some(ExprKind::Match {
            scrutinee: opt.clone(),
            arms: vec![some_arm, none_arm],
        })
    }

    /// Build the `ForLoop` node for a `find_map(iter, |x| body)` where `body`
    /// already evaluates to an `Option<U>`. `args ≈ [iter, closure]`. The loop
    /// folds an `Option` accumulator, keeping the first `Some`: once the
    /// accumulator is `Some`, it is preserved; otherwise the closure body is
    /// evaluated on the current element.
    fn rewrite_find_map(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };
        // The result of `find_map` — and of the closure body — is `Option<U>`.
        let option_ty = app_ty.clone();

        let none_ctor = crate::names::core::option::Option::None::Constructor;
        let some_ctor = crate::names::core::option::Option::Some::Constructor;
        let some_field = crate::names::core::option::Option::Some::_0;

        // The accumulator binder threaded by the loop state.
        let acc_id: LocalId = "__find_map_acc".into();
        let acc_pat = PatKind::var_pat(acc_id.clone()).promote(option_ty.clone(), span);
        let acc_expr = ExprKind::LocalId(acc_id).promote(option_ty.clone(), span);

        // Arm `Some(_) => __find_map_acc`
        let some_wild_pat = PatKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(some_field, PatKind::Wild.promote(option_ty.clone(), span))],
        }
        .promote(option_ty.clone(), span);
        let some_arm = Arm::non_guarded(some_wild_pat, acc_expr.clone(), span);

        // Arm `None => <closure.body>`
        let none_pat = PatKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
        }
        .promote(option_ty.clone(), span);
        let none_arm = Arm::non_guarded(none_pat, body.clone(), span);

        // `match __find_map_acc { Some(_) => __find_map_acc, None => <body> }`
        let match_body = ExprKind::Match {
            scrutinee: acc_expr,
            arms: vec![some_arm, none_arm],
        }
        .promote(option_ty.clone(), span);

        Some(ExprKind::Loop {
            body: match_body,
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: none_expr_for_init(none_ctor, option_ty, span),
                body_pat: acc_pat,
            }),
            control_flow: None,
            label: None,
        })
    }

    /// Build the cons-list-building `ForLoop` for an
    /// `Iterator::collect(Iterator::map(iter, |x| body))`. `args ≈ [inner]`
    /// where `inner` (after peeling ascription/borrow) is the `map` call. The
    /// loop starts from an empty vector and, for each element, pushes the
    /// mapped value onto the accumulator.
    fn rewrite_map_collect(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [inner] = args else {
            return None;
        };
        // Reach the `map` application under any ascription/borrow.
        let map_app = peel_wrappers(inner);
        let ExprKind::App {
            head: map_head,
            args: map_args,
            ..
        } = &*map_app.kind
        else {
            return None;
        };
        // Confirm the inner call really is `Iterator::map`.
        let ExprKind::GlobalId(map_g) = &*map_head.kind else {
            return None;
        };
        if !map_g.to_debug_string().ends_with("Iterator::map") {
            return None;
        }
        let [iter, closure] = &map_args[..] else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };

        // The collected result type (`Vec<U>`/array) is the App's type, and
        // also the loop-accumulator type.
        let vec_ty = app_ty.clone();

        // The accumulator binder threaded by the loop state.
        let acc_id: LocalId = "__map_acc".into();
        let acc_pat = PatKind::var_pat(acc_id.clone()).promote(vec_ty.clone(), span);
        let acc_expr = ExprKind::LocalId(acc_id).promote(vec_ty.clone(), span);

        // Empty Seq: `array_nil()`, which the printer renders as
        // `rust_primitives__hax__array_nil()`.
        let init_expr = Expr::standalone_fn_app(
            crate::names::rust_primitives::hax::array_nil,
            vec![],
            vec![],
            vec_ty.clone(),
            span,
        );

        // `array_cons(<closure.body>, __map_acc)` — cons the mapped element
        // onto the accumulator Seq (reversed order, which is fine
        // symbolically).
        let cons_body = Expr::standalone_fn_app(
            crate::names::rust_primitives::hax::array_cons,
            vec![],
            vec![body.clone(), acc_expr],
            vec_ty.clone(),
            span,
        );

        Some(ExprKind::Loop {
            body: cons_body,
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: init_expr,
                body_pat: acc_pat,
            }),
            control_flow: None,
            label: None,
        })
    }

    /// Build the scalar `if` for a `bool::then(cond, || body)`.
    /// `args ≈ [cond, closure]` where the closure takes *no* parameters and
    /// returns the value. Result is `if cond { Some(<closure.body>) } else
    /// { None }`, matching `bool::then`'s `Option` semantics. This appears
    /// nested inside `find_map` bodies; the recursive visiting in
    /// [`AstVisitorMut::visit_expr`] rewrites those before this node is lifted.
    fn rewrite_bool_then(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [cond, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        // `then`'s closure takes no meaningful arguments. In Rust it is written
        // `|| body`, but the frontend lowers `FnOnce()` to a closure carrying a
        // single (unit) parameter, so accept either shape — the parameter is
        // unused, so we drop it.
        if params.len() > 1 {
            return None;
        }
        // The App's type is `Option<T>` (the produced value type).
        let option_ty = app_ty.clone();

        let some_ctor = crate::names::core::option::Option::Some::Constructor;
        let none_ctor = crate::names::core::option::Option::None::Constructor;
        let some_field = crate::names::core::option::Option::Some::_0;

        // `Some(<closure.body>)`
        let some_expr = ExprKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(some_field, body.clone())],
            base: None,
        }
        .promote(option_ty.clone(), span);

        // `None`
        let none_expr = ExprKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
            base: None,
        }
        .promote(option_ty, span);

        Some(ExprKind::If {
            condition: cond.clone(),
            then: some_expr,
            else_: Some(none_expr),
        })
    }

    /// Build the no-accumulator `ForLoop` for an `for_each(iter, |x| body)`.
    /// `args ≈ [iter, closure]`; `body` returns unit. The loop has no
    /// functional state (`state: None`): the printer threads unit through the
    /// `unroll_for_loop_nostate` path, running `body` for its effects on each
    /// element.
    fn rewrite_for_each(span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };
        let _ = span;
        Some(ExprKind::Loop {
            body: body.clone(),
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: None,
            control_flow: None,
            label: None,
        })
    }

    /// Build the cons-list-building `ForLoop` for a
    /// `filter_map(iter, |x| body)` where `body : Option<U>`. `args ≈ [iter,
    /// closure]`. The loop starts from an empty Seq and, for each element,
    /// `match`es the closure body: a `Some(y)` conses `y` onto the
    /// accumulator, a `None` keeps the accumulator unchanged.
    fn rewrite_filter_map(app_ty: &Ty, span: Span, args: &[Expr]) -> Option<ExprKind> {
        let [iter, closure] = args else {
            return None;
        };
        let ExprKind::Closure { params, body, .. } = &*closure.kind else {
            return None;
        };
        let [elem_pat] = &params[..] else {
            return None;
        };

        // The collected result type (`Vec<U>`/Seq) is the App's type, and also
        // the loop-accumulator type.
        let vec_ty = app_ty.clone();
        // The closure body's type is `Option<U>`; `U` is the Some payload.
        let option_ty = body.ty.clone();
        let payload_ty = option_payload_ty(&option_ty);

        let some_ctor = crate::names::core::option::Option::Some::Constructor;
        let none_ctor = crate::names::core::option::Option::None::Constructor;
        let some_field = crate::names::core::option::Option::Some::_0;

        // The accumulator binder threaded by the loop state.
        let acc_id: LocalId = "__filter_map_acc".into();
        let acc_pat = PatKind::var_pat(acc_id.clone()).promote(vec_ty.clone(), span);
        let acc_expr = ExprKind::LocalId(acc_id).promote(vec_ty.clone(), span);

        // Empty Seq: `array_nil()`.
        let init_expr = Expr::standalone_fn_app(
            crate::names::rust_primitives::hax::array_nil,
            vec![],
            vec![],
            vec_ty.clone(),
            span,
        );

        // Arm `Some(y) => array_cons(y, __filter_map_acc)`
        let payload_id: LocalId = "__filter_map_y".into();
        let some_pat = PatKind::Construct {
            constructor: some_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![(
                some_field,
                PatKind::var_pat(payload_id.clone()).promote(payload_ty.clone(), span),
            )],
        }
        .promote(option_ty.clone(), span);
        let payload_expr = ExprKind::LocalId(payload_id).promote(payload_ty, span);
        let cons_expr = Expr::standalone_fn_app(
            crate::names::rust_primitives::hax::array_cons,
            vec![],
            vec![payload_expr, acc_expr.clone()],
            vec_ty.clone(),
            span,
        );
        let some_arm = Arm::non_guarded(some_pat, cons_expr, span);

        // Arm `None => __filter_map_acc`
        let none_pat = PatKind::Construct {
            constructor: none_ctor,
            is_record: false,
            is_struct: false,
            fields: vec![],
        }
        .promote(option_ty, span);
        let none_arm = Arm::non_guarded(none_pat, acc_expr, span);

        // `match <closure.body> { Some(y) => array_cons(y, acc), None => acc }`
        let match_body = ExprKind::Match {
            scrutinee: body.clone(),
            arms: vec![some_arm, none_arm],
        }
        .promote(vec_ty.clone(), span);

        Some(ExprKind::Loop {
            body: match_body,
            kind: Box::new(LoopKind::ForLoop {
                pat: elem_pat.clone(),
                iterator: iter.clone(),
            }),
            state: Some(LoopState {
                init: init_expr,
                body_pat: acc_pat,
            }),
            control_flow: None,
            label: None,
        })
    }
}

/// Helper: build a fresh `None` expression for the `find` loop initial state.
fn none_expr_for_init(none_ctor: GlobalId, option_ty: Ty, span: Span) -> Expr {
    ExprKind::Construct {
        constructor: none_ctor,
        is_record: false,
        is_struct: false,
        fields: vec![],
        base: None,
    }
    .promote(option_ty, span)
}

impl AstVisitorMut for ProverifCombinatorsToLoopsVisitor {
    setup_error_handling_impl!();

    fn visit_expr(&mut self, expr: &mut Expr) {
        // Recurse into children first so nested combinators are rewritten and
        // any closure bodies are visited before we lift this node.
        self.visit_inner(expr);

        let ExprKind::App { head, args, .. } = &*expr.kind else {
            return;
        };
        let Some(combinator) = classify(head) else {
            return;
        };
        let app_ty = expr.ty.clone();
        let span = expr.meta.span;
        let new_kind = match combinator {
            Combinator::Fold => {
                ProverifCombinatorsToLoopsVisitor::rewrite_fold(&app_ty, span, args)
            }
            Combinator::Find => {
                ProverifCombinatorsToLoopsVisitor::rewrite_find(&app_ty, span, args)
            }
            Combinator::Any => ProverifCombinatorsToLoopsVisitor::rewrite_any(span, args),
            Combinator::OptionMap => {
                ProverifCombinatorsToLoopsVisitor::rewrite_option_map(&app_ty, span, args)
            }
            Combinator::FindMap => {
                ProverifCombinatorsToLoopsVisitor::rewrite_find_map(&app_ty, span, args)
            }
            Combinator::MapCollect => {
                ProverifCombinatorsToLoopsVisitor::rewrite_map_collect(&app_ty, span, args)
            }
            Combinator::BoolThen => {
                ProverifCombinatorsToLoopsVisitor::rewrite_bool_then(&app_ty, span, args)
            }
            Combinator::ForEach => {
                ProverifCombinatorsToLoopsVisitor::rewrite_for_each(span, args)
            }
            Combinator::FilterMap => {
                ProverifCombinatorsToLoopsVisitor::rewrite_filter_map(&app_ty, span, args)
            }
        };
        if let Some(new_kind) = new_kind {
            *expr = new_kind.promote(app_ty, span);
        }
    }
}

impl Phase for ProverifCombinatorsToLoops {
    fn apply(&self, items: &mut Vec<Item>) {
        ProverifCombinatorsToLoopsVisitor::default().visit(items)
    }
}
