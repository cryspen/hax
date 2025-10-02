#![feature(coverage_attribute)]
#![allow(unused_attributes)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod attr;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod auxiliary;
/* Modules that are commented out are not used by any test target.
They are kept in case they need to be added to a target in the future. */
// mod branch;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax"
))]
mod abort;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax"
))]
mod assert;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
#[path = "assert-ne.rs"]
mod assert_ne;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod assert_not;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod condition;
mod mcdc;
// mod async_block;
// mod async_closure;
// mod r#async;
// mod async2;
// mod await_ready;
// mod bad_counter_ids;
// mod bench;
// mod closure_bug;
// mod closure_macro_async;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod closure_macro;
// mod closure;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod closure_unit_return;
#[cfg(any(feature = "json", feature = "lean"))]
mod color;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod conditions;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar"))]
#[path = "continue.rs"]
mod continue_;
// mod coroutine;
// mod coverage_attr_closure;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod dead_code;
// #[path = "discard-all-issue-133606.rs"]
// mod discard_all_issue_133606;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod drop_trait;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod fn_sig_into_try;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod generics;
// #[path = "generic-unused-impl.rs"]
// mod generic_unused_impl;
// mod holes;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
#[path = "if.rs"]
mod if_;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod if_else;
#[cfg(any(feature = "json", feature = "lean"))]
mod if_not;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod ignore_map;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod ignore_run;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
#[path = "inline-dead.rs"]
mod inline_dead;
// mod inline_mixed;
#[cfg(any(feature = "json", feature = "lean"))]
mod inline;
#[cfg(any(feature = "json", feature = "lean"))]
mod inner_items;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
#[path = "issue-83601.rs"]
mod issue_83601;
// #[path = "issue-84561.rs"]
// mod issue_84561;
// #[path = "issue-85461.rs"]
// mod issue_85461;
// #[path = "issue-93054.rs"]
// mod issue_93054;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod lazy_boolean;
#[cfg(any(feature = "json", feature = "lean"))]
mod let_else_loop;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod long_and_wide;
#[cfg(any(feature = "json", feature = "lean"))]
#[path = "loop-break.rs"]
mod loop_break;
#[cfg(any(feature = "json", feature = "lean"))]
mod loop_break_value;
#[cfg(any(feature = "json", feature = "lean"))]
mod loops_branches;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod macro_in_closure;
// mod macro_name_span;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod match_or_pattern;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar"))]
mod nested_loops;
// #[path = "no-core.rs"]
// mod no_core;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod no_cov_crate;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod no_spans;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod no_spans_if_not;
#[cfg(any(feature = "json", feature = "fstar"))]
mod overflow;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax"
))]
mod panic_unwind;
#[cfg(any(feature = "json", feature = "fstar", feature = "coq"))]
mod partial_eq;
#[cfg(any(feature = "json", feature = "lean"))]
mod simple_loop;
#[cfg(any(feature = "json", feature = "lean"))]
mod simple_match;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod sort_groups;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod test_harness;
#[cfg(any(feature = "json", feature = "lean"))]
mod tight_inf_loop;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod trivial;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar", feature = "coq"))]
mod try_error_result;
#[cfg(any(feature = "json"))]
mod unicode;
// mod unreachable;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar"))]
mod unused;
#[cfg(any(
    feature = "json",
    feature = "lean",
    feature = "fstar",
    feature = "fstar-lax",
    feature = "coq"
))]
mod unused_mod;
// mod uses_crate;
// mod uses_inline_crate;
#[cfg(any(feature = "json", feature = "lean"))]
#[path = "while.rs"]
mod while_;
#[cfg(any(feature = "json", feature = "lean", feature = "fstar"))]
mod while_early_ret;
// mod r#yield;
