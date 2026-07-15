//! The ProVerif backend.
//!
//! This is a port of the legacy OCaml printer at
//! `engine/backends/proverif/proverif_backend.ml` to the rust-engine
//! "Rust backend" architecture. The OCaml side now only declares the
//! `InputLanguage` feature set and applies the phase pipeline; all printing
//! happens in this file.
//!
//! Stage 1 is strict parity with the legacy OCaml output: the same `lib.pvl`
//! file, the same constructor scheme, the same baked-in 14-line preamble.
//! Feature extensions land in Stage 2.
//!
//! Method-by-method mapping to the legacy OCaml printer
//! (`engine/backends/proverif/proverif_backend.ml`):
//!
//! | OCaml | Rust |
//! |---|---|
//! | `ty` (732-758), `ty_bool` (340), `ty_int` (341) | [`fn ty`](ProVerifPrinter::ty) |
//! | `pat'` (279-338) | [`fn pat`](ProVerifPrinter::pat) |
//! | `expr'` (374-476), `expr_app` (357-372), `expr` (703-730) | [`fn expr`](ProVerifPrinter::expr) |
//! | `item_unwrapped` (480-642) — Fn / Type / Quote | [`fn item`](ProVerifPrinter::item) |
//! | `concrete_ident'` (653-660) | flattened by `RenderView::separator = "__"` |
//! | Preamble (811-832) | the [`HEADER`] string constant |

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use super::prelude::*;
use crate::ast::span::Span;
use crate::ast::visitors::AstVisitor;
use crate::phase::*;
use crate::printer::render_with_span_positions;
use camino::Utf8PathBuf;
use hax_lib_macros_types::AttrPayload;
use hax_types::engine_api::{File, SourceMap};

/// Constructor IDs used by the ProVerif special-cases. Mirror the OCaml
/// `Global_ident.eq_name`-style equality tests.
mod names {
    pub use crate::names::core::clone::Clone::clone;
    pub use crate::names::core::convert::Into::into;
    pub use crate::names::core::ops::deref::Deref::deref;
    pub use crate::names::core::option::Option::None::Constructor as OptionNone;
    pub use crate::names::core::option::Option::Some::Constructor as OptionSome;
    pub use crate::names::core::result::Result::Err::Constructor as ResultErr;
    pub use crate::names::core::result::Result::Ok::Constructor as ResultOk;
    pub use crate::names::rust_primitives::hax::never_to_any;
    pub use crate::names::rust_primitives::hax::{cast_op, logical_op_and, logical_op_or};
    pub use crate::names::rust_primitives::unsize;
}

/// The ProVerif printer.
#[setup_printer_struct]
#[derive(Default, Clone)]
pub struct ProVerifPrinter {
    /// `LocalId`s that should be rendered as `bitstring_default()`
    /// rather than as their literal name. Populated up-front from every
    /// item's `GenericParamKind::Const` so that references to const
    /// generics (`fn f<const N: usize>(x: [T; N]) -> ...` writing `N`
    /// in the body) survive into a parseable output. ProVerif has no
    /// generic-parameter notion; after Stage 2.0 the surrounding type
    /// collapses to `bitstring` anyway, so the runtime value is
    /// symbolically irrelevant.
    erased_const_generics: HashSet<LocalId>,
}

/// Bundled `primitives.pvl` — declarations for the stable hax extraction
/// surface (`rust_primitives::*`, the `core::num/ops/cmp/slice` trait
/// roots, `hax_lib::*` helpers, tuple constructors, panic sink, etc.).
///
/// Lives next to this file at `hax-lib/proof-libs/proverif/primitives.pvl`.
/// Embedded here so the printer can parse it to know which names *not*
/// to re-declare in the auto-declared external block.
const PRIMITIVES_PVL: &str = include_str!("../../../hax-lib/proof-libs/proverif/primitives.pvl");

/// Preamble baked into every `lib.pvl` file.
///
/// Stage 2.0 collapses every Rust type to ProVerif `bitstring`. Booleans
/// become `True()`/`False()` data constructors and integer literals are
/// wrapped in `nat_lit(N)` so they land in the same universe.
const HEADER: &str = "\
(*
  Run with:
    proverif -lib <hax>/hax-lib/proof-libs/proverif/primitives.pvl lib.pvl

  The `primitives.pvl` library ships with hax and supplies
  everything the extracted file references that isn't defined
  below: the public channel `c`, the `construct_fail` sink,
  `bitstring_default`/`bitstring_err`, the `Some`/`None`/
  `True`/`False`/`nat_lit` constructors, `logical_and`/`or`, and
  every `rust_primitives::*` / `core::*` / `hax_lib::*` opaque
  function the extraction surface needs.

  Any symbol this file references but does NOT define, and that is
  not in `primitives.pvl`, is listed in the companion
  `missingdecl.pvl`. That file is a DIAGNOSTIC, not part of the
  model: each entry must be supplied by hand or by another crate's
  extraction (e.g. a separately-extracted dependency). The goal is
  for `missingdecl.pvl` to be EMPTY — anything in it is a reachable
  definition that was silently stubbed out.
*)

";

const INDENT: isize = 2;

/// Depth to which `for`-loops over a collection are unrolled in the
/// ProVerif printer. ProVerif has no loops or recursion, so a range/
/// collection `for` loop is emitted as a fixed `LOOP_BOUND`-deep
/// unrolling that *destructures* the iterator Seq (a cons-list over the
/// `array_cons`/`array_nil` constructors declared in `primitives.pvl`),
/// peeling real element values off the front. The loop is done once the
/// Seq is `array_nil`, and fails with `bitstring_err()` if it would run
/// more than `LOOP_BOUND` iterations. This is a precise model up to
/// `LOOP_BOUND` iterations, and uses *no integer arithmetic*.
const LOOP_BOUND: usize = 3;

impl RenderView for ProVerifPrinter {
    fn reserved_keywords() -> &'static HashSet<String> {
        static SET: OnceLock<HashSet<String>> = OnceLock::new();
        SET.get_or_init(|| {
            // Mirrors `ProVerifNamePolicy.reserved_words` in
            // `engine/backends/proverif/proverif_backend.ml:102-104`.
            [
                "among",
                "axiom",
                "channel",
                "choice",
                "clauses",
                "const",
                "def",
                "diff",
                "do",
                "elimtrue",
                "else",
                "equation",
                "equivalence",
                "event",
                "expand",
                "fail",
                "for",
                "forall",
                "foreach",
                "free",
                "fun",
                "get",
                "if",
                "implementation",
                "in",
                "inj-event",
                "insert",
                "lemma",
                "let",
                "letfun",
                "letproba",
                "new",
                "noninterf",
                "noselect",
                "not",
                "nounif",
                "or",
                "otherwise",
                "out",
                "param",
                "phase",
                "pred",
                "proba",
                "process",
                "proof",
                "public vars",
                "putbegin",
                "query",
                "reduc",
                "restriction",
                "secret",
                "select",
                "set",
                "suchthat",
                "sync",
                "table",
                "then",
                "type",
                "weaksecret",
                "yield",
            ]
            .into_iter()
            .map(|s| s.to_string())
            .collect()
        })
    }

    /// The legacy OCaml backend flattens namespaces with `__` (see
    /// `proverif_backend.ml:653-660`).
    fn separator(&self) -> &str {
        "__"
    }

    /// Escape so the rendered string is a *valid ProVerif identifier*.
    ///
    /// ProVerif's lexer rejects identifiers that:
    ///  - start with an underscore (`_msg` is *not* an identifier — the
    ///    lone `_` is a wildcard, and `_` + anything is a syntax error),
    ///  - clash with one of the reserved keywords (`channel`, `let`, …).
    ///
    /// Strategy: replace illegal characters with `_`, then collapse the
    /// leading-underscore problem by prepending a stable letter `u`, then
    /// handle keyword clashes with a `_kw` *suffix* (a prefix would just
    /// re-introduce the leading-underscore problem).
    fn escape(id: &str) -> String {
        let id = id.replace([' ', '<', '>'], "_");
        if id.is_empty() {
            return "_ERROR_EMPTY_ID_".to_string();
        }
        let id = if id.starts_with('_') {
            format!("u{id}")
        } else {
            id
        };
        if Self::is_reserved_keyword(&id) {
            format!("{id}_kw")
        } else {
            id
        }
    }
}

impl Printer for ProVerifPrinter {
    // ProVerif's flattened identifiers (`bertie__tls13crypto__AeadKeyIV__…`)
    // are long, so an 80-column page forces nearly every declaration to
    // break. A wider page lets short declarations/calls collapse onto one
    // line while still breaking the genuinely long ones.
    const RENDER_WIDTH: usize = 100;
}

impl ProVerifPrinter {
    /// Returns the joined identifier used by ProVerif declarations. Mirrors
    /// `print#concrete_ident` in the legacy printer.
    fn render_id(&self, id: &GlobalId) -> String {
        self.render_string(&id.view())
    }

    /// Name of the per-field destructor function emitted by `fun_and_reduc`.
    ///
    /// It must match exactly what the user's field-projection expressions
    /// render as — when hax extracts `self.psk_mode`, the AST has an
    /// `ExprKind::App` whose head is the `GlobalId` of the field, which
    /// renders to e.g. `bertie__tls13crypto__Algorithms__Algorithms__psk_mode`.
    /// Therefore the destructor's name needs to be that same string, so
    /// the call site resolves to a real function.
    ///
    /// The legacy OCaml printer named the destructor
    /// `accessor_<base>__<field>` and emitted a separate field-projection
    /// rewrite in the printer to call that. The new uniform-bitstring
    /// printer just uses the field's rendered identifier directly, which
    /// is what the auto-decl pass would otherwise declare as an opaque
    /// `fun [data].` for the same call site.
    fn accessor_name(&self, _base: &str, field: &GlobalId) -> String {
        self.render_id(field)
    }
}

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
const _: () = {
    macro_rules! emit_error {
        ($($tt:tt)*) => {
            disambiguated_todo!($($tt)*)
        };
    }
    macro_rules! line {
        ($($tt:tt)*) => {
            disambiguated_line!($($tt)*)
        };
    }
    macro_rules! concat {
        ($($tt:tt)*) => {
            disambiguated_concat!($($tt)*)
        };
    }

    // Print a separated list of ToDocument values, joined by `, `.
    macro_rules! comma_sep {
        ($it:expr) => {
            intersperse!($it, docs![",", line!()])
        };
    }

    // Wrap an already-built (typically comma-separated) document in
    // parentheses with adaptive Wadler-style layout: the whole thing stays
    // on one line when it fits the page, and otherwise breaks after `(`,
    // indenting the contents by `INDENT` and dropping `)` back onto its own
    // line. ProVerif is whitespace-insensitive between tokens, so this is a
    // purely cosmetic reflow.
    //
    //   flat:   (a, b, c)
    //   broken: (
    //             a,
    //             b,
    //             c
    //           )
    macro_rules! paren_doc {
        ($d:expr) => {
            docs!["(", docs![line_!(), $d].nest(INDENT), line_!(), ")"].group()
        };
    }

    // Build a grouped, parenthesized, comma-separated list from an iterator
    // of `ToDocument` values. Combines [`comma_sep!`] and [`paren_doc!`].
    macro_rules! paren_list {
        ($it:expr) => {
            paren_doc!(comma_sep!($it))
        };
    }

    impl ProVerifPrinter {
        /// Emit a syntactically valid placeholder in expression position
        /// alongside a diagnostic. ProVerif comments (`(* ... *)`) aren't
        /// terms, so we surface `bitstring_err()` (declared in the preamble)
        /// instead — that keeps the surrounding letfun parseable.
        fn expr_error_placeholder<A: 'static + Clone>(&self, message: &str) -> DocBuilder<A> {
            <Self as PrettyAst<A>>::emit_diagnostic(
                self,
                hax_types::diagnostics::Kind::Unimplemented {
                    issue_id: None,
                    details: Some(message.into()),
                },
            );
            docs!["bitstring_err()", " (* ", message.to_string(), " *)"]
        }

        /// A "trivial" binder is one whose rendered pattern is just `x`
        /// (or `_`) — i.e., a pattern that cannot fail at runtime. ProVerif
        /// rejects `else` on these, and they never need a fallback because
        /// they always match.
        ///
        /// We mirror the special cases in `pat`: `ResultOk(inner)` and
        /// `Ascription` are transparent (they just render their inner pat),
        /// so trivialness propagates through them.
        fn is_trivial_binder(pat: &Pat) -> bool {
            match &*pat.kind {
                PatKind::Wild => true,
                PatKind::Binding {
                    sub_pat: None,
                    mode: BindingMode::ByValue,
                    mutable: false,
                    ..
                } => true,
                PatKind::Ascription { pat, .. } => Self::is_trivial_binder(pat),
                PatKind::Construct {
                    constructor,
                    fields,
                    ..
                } if *constructor == names::ResultOk => fields
                    .first()
                    .map(|(_, inner)| Self::is_trivial_binder(inner))
                    .unwrap_or(true),
                _ => false,
            }
        }

        /// Whether `expr` renders to a *self-delimiting* ProVerif term — one
        /// that needs no surrounding parentheses when it appears as the RHS of
        /// a `let`, as a branch of the `if`-rewrite, or as a match-arm body.
        ///
        /// Atomic forms are variables, literals, and (possibly nested through
        /// the identity passthroughs `into`/`clone`/…) function- and
        /// constructor-applications `f(...)` / `C(...)` / `bitstring_err()`,
        /// all of which are bounded by their own parentheses. Compound forms
        /// (`let … in …`, the `if`-rewrite, match-chains, loop unrollings,
        /// verbatim quotes) are NOT atomic: they end in a position where a
        /// following `else`/`in` could rebind, so they keep the parens that
        /// isolate them. Deliberately conservative — when unsure, returns
        /// `false` (keeps the parens), so dropping them is always sound.
        fn expr_is_atomic(expr: &Expr) -> bool {
            match &*expr.kind {
                ExprKind::LocalId(_) | ExprKind::GlobalId(_) | ExprKind::Literal(_) => true,
                ExprKind::Ascription { e, .. } => Self::expr_is_atomic(e),
                // Identity passthroughs render their single argument verbatim,
                // so atomicity propagates through them (see `expr`).
                ExprKind::App { head, args, .. }
                    if matches!(&*head.kind, ExprKind::GlobalId(g)
                        if *g == names::into
                            || *g == names::clone
                            || *g == names::unsize
                            || *g == names::deref
                            || *g == names::cast_op) =>
                {
                    args.first().map(Self::expr_is_atomic).unwrap_or(true)
                }
                // Any other application renders `f(args)` / `f()` — and the
                // `logical_and`/`logical_or`/`never_to_any` special cases all
                // render as function applications too: self-delimiting.
                ExprKind::App { .. } => true,
                // `Ok(inner)` strips to `inner`; everything else
                // (`Err`→`bitstring_err()`, `None()`, `Some(_)`, `C(_)`) is a
                // constructor application.
                ExprKind::Construct {
                    constructor,
                    fields,
                    ..
                } if *constructor == names::ResultOk => fields
                    .first()
                    .map(|(_, inner)| Self::expr_is_atomic(inner))
                    .unwrap_or(true),
                ExprKind::Construct { .. } => true,
                // Cons-list `array_cons(...)` form.
                ExprKind::Array(_) => true,
                _ => false,
            }
        }

        /// Render `expr` in a position that would otherwise be parenthesized,
        /// dropping the parens when [`Self::expr_is_atomic`] proves they are
        /// redundant. Used for `let` RHSs, the `if`-rewrite branches, and
        /// match-arm bodies — turning `let x = (f(a)) in` into the readable
        /// `let x = f(a) in` while keeping parens around compound terms.
        fn paren_unless_atomic<A: 'static + Clone>(&self, expr: &Expr) -> DocBuilder<A> {
            if Self::expr_is_atomic(expr) {
                docs![expr]
            } else {
                docs![expr].parens()
            }
        }

        /// Print one match-arm as an `if-let` chain piece. Mirrors
        /// `match_arm` (`proverif_backend.ml:229-247`).
        ///
        /// For failable arms we wrap the body in `( ... )` so that a
        /// subsequent `else N` in the enclosing Match chain binds to *this*
        /// arm's `let`, not to some inner destructure inside `body`.
        /// Arms whose rendered pattern is a trivial binder (e.g. `Ok(th)`
        /// → `th`) never fail, so we omit the parens (which would let a
        /// subsequent `else` attach to this `let` — and ProVerif rejects
        /// `else` on a simple-binder let).
        fn match_arm<A: 'static + Clone>(
            &self,
            scrutinee: &Expr,
            arm: &Arm,
            is_last: bool,
        ) -> DocBuilder<A> {
            match &*arm.pat.kind {
                PatKind::Wild => docs![&arm.body],
                // A `Result::Err` arm collapses to a bare `bitstring_err()` only
                // when it is the final (fallback) arm of the chain — there it
                // stands in for "no further arm matched -> fail". When such an
                // arm is NOT last (e.g. `match r { Err(_) => false, Ok(x) => .. }`)
                // a bare `bitstring_err()` is wrong twice over: the following
                // `else` has no `let` to bind to (a ProVerif syntax error), and
                // the arm body (here `false`) would be discarded. So we fall
                // through and render it as an ordinary destructuring arm.
                PatKind::Construct { constructor, .. }
                    if is_last && *constructor == names::ResultErr =>
                {
                    docs!["bitstring_err()"]
                }
                _ => {
                    let pat: DocBuilder<A> = match &*arm.pat.kind {
                        PatKind::Constant { lit } => docs!["=", lit].parens(),
                        _ => docs![&arm.pat],
                    };
                    let body = if Self::is_trivial_binder(&arm.pat) {
                        docs![&arm.body]
                    } else {
                        self.paren_unless_atomic(&arm.body)
                    };
                    docs![
                        "let ",
                        pat,
                        " = ",
                        docs![scrutinee],
                        " in",
                        docs![line!(), body].nest(INDENT).group()
                    ]
                }
            }
        }

        /// Emit one level `k` of the bounded `for`-loop unrolling. `seq` /
        /// `acc` are the *textual* names of the current iterator Seq and
        /// accumulator bindings (`bl__seq{k}` / `bl__acc{k}`). The prefix has
        /// no *leading* underscore: ProVerif's lexer rejects identifiers that
        /// begin with `_`.
        ///
        /// The iterator is modelled as a cons-list ("Seq") over the
        /// `array_cons` / `array_nil` constructors. At each level we
        /// *destructure* the head element off the Seq (`let
        /// array_cons(<pat>, bl__seq{k+1}) = <seq>`): on success we bind the
        /// (real) head value, run the body once, and recurse one level
        /// deeper; the `else` branch (the Seq is `array_nil`, i.e. not a
        /// `cons`) means "done" and yields the accumulator. At `LOOP_BOUND` a
        /// still-present `(N+1)`th element fails with `bitstring_err()`;
        /// otherwise the loop is done. *No integers* are used.
        fn unroll_for_loop_level<A: 'static + Clone>(
            &self,
            k: usize,
            seq: &str,
            acc: &str,
            pat: &Pat,
            body: &Expr,
            state: &LoopState,
        ) -> DocBuilder<A> {
            if k >= LOOP_BOUND {
                // Overflow terminal: the loop ran `LOOP_BOUND` times; if the
                // Seq still has a head element, the bound is exceeded.
                return docs![
                    "let rust_primitives__hax__array_cons(bl__xh, bl__xt) = ",
                    seq.to_string(),
                    " in bitstring_err() else (",
                    acc.to_string(),
                    ")"
                ];
            }
            let next_seq = format!("bl__seq{}", k + 1);
            let next_acc = format!("bl__acc{}", k + 1);
            let inner: DocBuilder<A> =
                self.unroll_for_loop_level(k + 1, &next_seq, &next_acc, pat, body, state);
            docs![
                "let rust_primitives__hax__array_cons(",
                docs![pat],
                ", ",
                next_seq.clone(),
                ") = ",
                seq.to_string(),
                " in (let ",
                docs![&state.body_pat],
                " = ",
                acc.to_string(),
                " in",
                hardline!(),
                "let ",
                next_acc.clone(),
                " = (",
                docs![body],
                ") in",
                hardline!(),
                inner,
                ") else (",
                acc.to_string(),
                ")"
            ]
        }

        /// Emit the full bounded unrolling for a
        /// `for <pat> in <iterator> { <body> }` loop with functional
        /// `state` (`init` + `body_pat`). See [`Self::unroll_for_loop_level`].
        fn unroll_for_loop<A: 'static + Clone>(
            &self,
            pat: &Pat,
            iterator: &Expr,
            body: &Expr,
            state: &LoopState,
        ) -> DocBuilder<A> {
            let inner: DocBuilder<A> =
                self.unroll_for_loop_level(0, "bl__seq0", "bl__acc0", pat, body, state);
            docs![
                "(let bl__seq0 = (",
                docs![iterator],
                ") in let bl__acc0 = (",
                docs![&state.init],
                ") in ",
                hardline!(),
                inner,
                ")"
            ]
        }

        /// One unrolling level for a *no-accumulator* (side-effecting)
        /// `for <pat> in <coll> { <body> }` loop, i.e. `state: None`. Same
        /// `array_cons`-destructuring Seq chain as
        /// [`Self::unroll_for_loop_level`], but with no `acc` threading: the
        /// "done" result is unit (`rust_primitives__hax__Tuple0__Tuple0`) and
        /// each iteration runs `body` for its effects (bound to a throwaway
        /// `wildcard`).
        fn unroll_for_loop_nostate_level<A: 'static + Clone>(
            &self,
            k: usize,
            seq: &str,
            pat: &Pat,
            body: &Expr,
        ) -> DocBuilder<A> {
            if k >= LOOP_BOUND {
                // Overflow terminal: the Seq must be exhausted by now.
                return docs![
                    "let rust_primitives__hax__array_cons(bl__xh, bl__xt) = ",
                    seq.to_string(),
                    " in bitstring_err() else (rust_primitives__hax__Tuple0__Tuple0)"
                ];
            }
            let next_seq = format!("bl__seq{}", k + 1);
            let inner: DocBuilder<A> =
                self.unroll_for_loop_nostate_level(k + 1, &next_seq, pat, body);
            docs![
                "let rust_primitives__hax__array_cons(",
                docs![pat],
                ", ",
                next_seq.clone(),
                ") = ",
                seq.to_string(),
                " in (let wildcard = (",
                docs![body],
                ") in",
                hardline!(),
                inner,
                ") else (rust_primitives__hax__Tuple0__Tuple0)"
            ]
        }

        /// Emit the full bounded unrolling for a side-effecting
        /// `for <pat> in <iterator> { <body> }` loop with no functional state
        /// (`state: None`). See [`Self::unroll_for_loop_nostate_level`].
        fn unroll_for_loop_nostate<A: 'static + Clone>(
            &self,
            pat: &Pat,
            iterator: &Expr,
            body: &Expr,
        ) -> DocBuilder<A> {
            let inner: DocBuilder<A> = self.unroll_for_loop_nostate_level(0, "bl__seq0", pat, body);
            docs![
                "(let bl__seq0 = (",
                docs![iterator],
                ") in ",
                hardline!(),
                inner,
                ")"
            ]
        }

        /// Attach `span` as a `pretty` document annotation, but only when the
        /// printer's annotation type `A` is actually `Span` — which is the case
        /// during real rendering, since the [`Printer`] trait pins `A = Span`.
        /// The `PrettyAst<A>` methods are generic in `A`, so this guarded helper
        /// lets them record per-item provenance (harvested by
        /// [`crate::printer::SpanPositionRenderer`]) without constraining `A`;
        /// for any other `A` it is a no-op. Annotations never affect layout, so
        /// the rendered text is unchanged either way.
        fn annotate_with_span<A: 'static + Clone>(doc: DocBuilder<A>, span: Span) -> DocBuilder<A> {
            if std::any::TypeId::of::<A>() == std::any::TypeId::of::<Span>() {
                // SAFETY: `A == Span` (checked just above) and `Span: Copy`, so
                // reinterpreting the `Span` value as an `A` is a valid,
                // leak-free bitwise copy.
                let a: A = unsafe { std::mem::transmute_copy::<Span, A>(&span) };
                doc.annotate(a)
            } else {
                doc
            }
        }

        /// Emit a source-provenance comment `(* src: file:line name *)` above a
        /// generated declaration, tying the ProVerif output back to the Rust
        /// definition it came from (the side-by-side / explainability anchor).
        /// Only emitted for items carrying a real source span — phase-synthesized
        /// nodes (`Span::dummy()`, no on-disk file) get nothing.
        fn src_comment<A: 'static + Clone>(&self, span: Span, name: &GlobalId) -> DocBuilder<A> {
            if let Some(fs) = span.as_frontend_spans().first()
                && let Some(path) = fs.filename.to_path()
            {
                return docs![
                    format!(
                        "(* src: {}:{} {} *)",
                        path.display(),
                        fs.lo.line,
                        self.render_id(name)
                    ),
                    hardline!()
                ];
            }
            nil!()
        }

        /// Render the leading Rust doc comments (`///` / `//!`) of an item's
        /// attribute list as ProVerif `(* … *)` comment lines, so the
        /// generated model carries the same prose that documents the Rust
        /// source — the readability goal of side-by-side translation. Tool
        /// and Hax attributes carry no ProVerif meaning and are skipped.
        ///
        /// Each physical line of the doc body becomes its own `(* … *)` so we
        /// never hand the `pretty` layout engine a string with embedded
        /// newlines (it counts columns and would mislay the rest of the line).
        /// Any `(*` / `*)` appearing inside the prose is defused (`( *` / `* )`)
        /// so it can neither open nor prematurely close the surrounding
        /// ProVerif comment.
        fn doc_comments<A: 'static + Clone>(&self, attrs: &[Attribute]) -> DocBuilder<A> {
            let mut doc = nil!();
            for a in attrs {
                if let AttributeKind::DocComment { body, .. } = &a.kind {
                    let defuse = |s: &str| s.replace("*)", "* )").replace("(*", "( *");
                    if body.is_empty() {
                        doc = docs![doc, "(* *)", hardline!()];
                        continue;
                    }
                    for line in body.lines() {
                        doc = docs![
                            doc,
                            "(*",
                            if line.is_empty() {
                                String::new()
                            } else {
                                format!(" {} ", defuse(line.trim_end()))
                            },
                            "*)",
                            hardline!()
                        ];
                    }
                }
            }
            doc
        }

        /// Print the `fun ... [data].` declaration and the matching `reduc`
        /// lines that recover each field. Mirrors `fun_and_reduc` inside
        /// `item_unwrapped`. Stage 2.0: every constructor returns `bitstring`
        /// because the surface type collapses uniformly.
        fn fun_and_reduc<A: 'static + Clone>(
            &self,
            base_name: &GlobalId,
            variant: &Variant,
        ) -> DocBuilder<A> {
            let base = self.render_id(base_name);
            let constructor_name = self.render_id(&variant.name);
            let typed_args_vec: Vec<(GlobalId, Ty)> = variant
                .arguments
                .iter()
                .map(|(id, ty, _)| (*id, ty.clone()))
                .collect();
            let arg_types_doc = paren_list!(typed_args_vec.iter().map(|(_, ty)| docs![ty]));

            let fun_line = docs![
                "fun ",
                constructor_name.clone(),
                arg_types_doc,
                ": bitstring [data]."
            ];

            if typed_args_vec.is_empty() {
                return fun_line;
            }

            // The destructor's name is the field id itself (so the user's
            // `self.field` call site lines up — see `accessor_name`).
            // That means the `reduc forall ...;` header must NOT bind any
            // variable with the same rendered name, or ProVerif emits a
            // "rebound" warning and shadows the destructor function name
            // inside the rule. The forall-bound variables are LOCAL to the
            // rule and only need to be fresh w.r.t. the (fully-qualified,
            // global) accessor/constructor function symbols used in it, so we
            // give them short positional names `v_0`, `v_1`, … rather than the
            // fully-qualified field id — only globals deserve qualified names,
            // and the qualified form produced unreadable binders like
            // `libcrux_psq__aead__AEADError__Deserialize__0_v`.
            let bind_names: Vec<String> = (0..typed_args_vec.len())
                .map(|i| format!("v_{i}"))
                .collect();
            let fun_args_full: DocBuilder<A> = comma_sep!(
                typed_args_vec
                    .iter()
                    .enumerate()
                    .map(|(i, (_, ty))| { docs![bind_names[i].clone(), ": ", ty] })
            );
            let fun_args_names: DocBuilder<A> =
                comma_sep!((0..typed_args_vec.len()).map(|i| docs![bind_names[i].clone()]));

            let reduc_pieces: Vec<DocBuilder<A>> = typed_args_vec
                .iter()
                .enumerate()
                .map(|(i, (id, _ty))| {
                    let accessor = self.accessor_name(&base, id);
                    let constructor_call =
                        docs![constructor_name.clone(), paren_doc!(fun_args_names.clone())];
                    let accessor_call = docs![accessor, paren_doc!(constructor_call)];
                    docs![
                        docs!["reduc forall ", fun_args_full.clone()]
                            .nest(INDENT)
                            .group(),
                        ";",
                        docs![line!(), accessor_call, " = ", bind_names[i].clone()]
                            .nest(INDENT)
                            .group()
                    ]
                })
                .collect();
            let reduc_doc = intersperse!(reduc_pieces, docs![".", hardline!()]);

            docs![fun_line, hardline!(), reduc_doc, "."]
        }
    }

    impl<A: 'static + Clone> PrettyAst<A> for ProVerifPrinter {
        const NAME: &'static str = "ProVerif";

        /// We never want a `sorry`-style placeholder in ProVerif output —
        /// instead emit a tagged comment so the file still parses.
        fn todo_document(&self, message: &str, issue_id: Option<u32>) -> DocBuilder<A> {
            <Self as PrettyAst<A>>::emit_diagnostic(
                self,
                hax_types::diagnostics::Kind::Unimplemented {
                    issue_id,
                    details: Some(message.into()),
                },
            );
            docs!["(* TODO: ", message, " *)"]
        }

        fn module(&self, module: &Module) -> DocBuilder<A> {
            // ProVerif is single-file. Each module just lays its items down,
            // separated by hard newlines.
            let items = &module.items;
            docs![intersperse!(
                items.iter().map(|item| { item.to_document(self) }),
                hardline!()
            )]
        }

        fn global_id(&self, global_id: &GlobalId) -> DocBuilder<A> {
            docs![self.render_id(global_id)]
        }

        fn local_id(&self, local_id: &LocalId) -> DocBuilder<A> {
            // Const-generic params (`N` in `[T; N]`) survive as bare
            // `LocalId`s in expression position because Specialize
            // doesn't yet monomorphize them. They render as
            // `bitstring_default()` — the type collapses to `bitstring`,
            // so the runtime value is symbolically irrelevant.
            if self.erased_const_generics.contains(local_id) {
                return docs!["bitstring_default()"];
            }
            // Mirrors the OCaml `local_ident` override: strip `impl ...`
            // wrappers and replace spaces/`+` with `_` so the result is a
            // valid ProVerif identifier.
            let name = &local_id.0.to_string();
            let rendered = if let Some(rest) = name.strip_prefix("impl ") {
                let rest = rest.replace([' ', '+'], "_");
                format!("impl_{rest}")
            } else {
                name.clone()
            };
            docs![Self::escape(&rendered)]
        }

        fn literal(&self, literal: &Literal) -> DocBuilder<A> {
            docs![match literal {
                // ProVerif's lexer doesn't accept `"foo"` or `'c'` as
                // terms. Encode them as auto-declared opaque constants —
                // unique per literal value, so distinct strings stay
                // distinguishable in symbolic reasoning. The auto-decl
                // pass picks these up because they're referenced via the
                // synthesised name.
                Literal::String(symbol) => {
                    format!("string_lit__{}", sanitize_string_literal(symbol.as_ref()))
                }
                Literal::Char(c) => {
                    format!("char_lit__{}", sanitize_string_literal(&c.to_string()))
                }
                Literal::Bool(true) => "True()".to_string(),
                Literal::Bool(false) => "False()".to_string(),
                Literal::Int {
                    value, negative, ..
                } => {
                    // ProVerif's `nat` is unsigned; spell negative literals as
                    // `nat_lit(0 - N)` (the only way to coax a negative term
                    // into the universal bitstring encoding).
                    if *negative {
                        format!("nat_lit(0 - {value})")
                    } else {
                        format!("nat_lit({value})")
                    }
                }
                Literal::Float {
                    value, negative, ..
                } => {
                    // ProVerif has no floats. Encode as an opaque
                    // per-value const, same as strings.
                    let sign = if *negative { "neg_" } else { "" };
                    format!(
                        "float_lit__{sign}{}",
                        sanitize_string_literal(value.as_ref())
                    )
                }
            }]
        }

        fn primitive_ty(&self, _primitive_ty: &PrimitiveTy) -> DocBuilder<A> {
            // Stage 2.0 uniform-bitstring: every Rust scalar collapses to
            // ProVerif `bitstring`. Booleans/ints/etc. are encoded via the
            // `True()`/`False()`/`nat_lit(...)` constructors declared in the
            // preamble.
            docs!["bitstring"]
        }

        fn int_kind(&self, _int_kind: &IntKind) -> DocBuilder<A> {
            docs!["bitstring"]
        }

        fn float_kind(&self, _float_kind: &FloatKind) -> DocBuilder<A> {
            docs!["bitstring"]
        }

        fn symbol(&self, symbol: &Symbol) -> DocBuilder<A> {
            docs![Self::escape(symbol.as_ref())]
        }

        fn ty(&self, ty: &Ty) -> DocBuilder<A> {
            // Stage 2.0/2.1 uniform-bitstring: every type renders as
            // `bitstring`. `Param(_)` survives — Specialize doesn't
            // monomorphize generic *functions*, only specific named
            // arithmetic/conversion calls — but a `Param` in output position
            // is meaningless to ProVerif, so we still flatten to `bitstring`.
            match ty.kind() {
                TyKind::Ref { .. } => unreachable_by_invariant!(Drop_references),
                TyKind::RawPointer => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                TyKind::Dyn(_) => unreachable_by_invariant!(Reject_dyn),
                TyKind::Error(e) => docs![e],
                _ => docs!["bitstring"],
            }
        }

        fn pat(&self, pat: &Pat) -> DocBuilder<A> {
            // Mirrors `print#pat'` (`proverif_backend.ml:279-338`).
            match &*pat.kind {
                PatKind::Wild => docs!["wildcard: bitstring"],
                PatKind::Constant { lit } => docs!["=", lit].parens(),
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => match (mutable, mode, sub_pat) {
                    (true, _, _) => unreachable_by_invariant!(Local_mutation),
                    (false, BindingMode::ByRef(_), _) => unreachable_by_invariant!(Drop_references),
                    (false, BindingMode::ByValue, None) => docs![var],
                    (false, BindingMode::ByValue, Some(p)) => docs![var, ": ", &p.ty],
                },
                PatKind::Ascription { pat, ty: _ } => docs![pat],
                PatKind::Construct {
                    constructor,
                    fields: _,
                    is_record: _,
                    is_struct: _,
                } if *constructor == names::OptionNone => docs!["None()"],
                PatKind::Construct {
                    constructor,
                    fields,
                    is_record: _,
                    is_struct: _,
                } if *constructor == names::OptionSome => {
                    // After Stage 2.0 every payload is already a `bitstring`,
                    // so there is no `_to_bitstring`/`_from_bitstring` to
                    // unwrap.
                    if let Some((_, inner)) = fields.first() {
                        docs!["Some", docs![inner].parens()]
                    } else {
                        docs!["Some()"]
                    }
                }
                PatKind::Construct {
                    constructor,
                    fields,
                    is_record: _,
                    is_struct: _,
                } if *constructor == names::ResultOk => {
                    // `Ok(inner)` is replaced by its contents (lines 318-327).
                    if let Some((_, inner)) = fields.first() {
                        docs![inner]
                    } else {
                        docs![""]
                    }
                }
                PatKind::Construct {
                    constructor,
                    fields,
                    is_record: _,
                    is_struct: _,
                } => {
                    // Every field is rendered (as a wildcard binder for `_`), so a
                    // multi-field pattern always keeps the constructor's arity. An
                    // earlier "all fields wild -> emit no args" placeholder produced
                    // `Constructor()` (0 args), which ProVerif rejects on any
                    // multi-field constructor (e.g. a `(_, _)` tuple catch-all ->
                    // `Tuple2()`); emitting `Tuple2(wildcard, wildcard)` is the
                    // correct always-matching form.
                    let args = if fields.is_empty() {
                        nil!()
                    } else {
                        comma_sep!(fields.iter().map(|(_, p)| {
                            // tuple-elem patterns are emitted with their type
                            // ascription if they're bare bindings (matches
                            // `tuple_elem_pat'`).
                            match &*p.kind {
                                PatKind::Binding {
                                    sub_pat: None,
                                    var,
                                    mutable: false,
                                    mode: BindingMode::ByValue,
                                } => docs![var, ": ", &p.ty],
                                _ => docs![p],
                            }
                        }))
                    };
                    if fields.is_empty() {
                        docs![constructor, "()"]
                    } else {
                        docs![constructor, paren_doc!(args)]
                    }
                }
                PatKind::Or { .. } => {
                    // ProVerif has no or-patterns. Emit a wildcard so the
                    // enclosing `let pat = ... in ... else ...` still parses;
                    // also raise the diagnostic.
                    <Self as PrettyAst<A>>::emit_diagnostic(
                        self,
                        hax_types::diagnostics::Kind::Unimplemented {
                            issue_id: None,
                            details: Some("ProVerif backend does not support or-patterns".into()),
                        },
                    );
                    docs!["wildcard: bitstring"]
                }
                PatKind::Array { .. } => {
                    <Self as PrettyAst<A>>::emit_diagnostic(
                        self,
                        hax_types::diagnostics::Kind::Unimplemented {
                            issue_id: None,
                            details: Some(
                                "ProVerif backend does not support array patterns".into(),
                            ),
                        },
                    );
                    docs!["wildcard: bitstring"]
                }
                PatKind::Deref { .. } => unreachable_by_invariant!(Drop_references),
                PatKind::Resugared(_) => {
                    <Self as PrettyAst<A>>::emit_diagnostic(
                        self,
                        hax_types::diagnostics::Kind::Unimplemented {
                            issue_id: None,
                            details: Some(
                                "ProVerif backend does not support resugared patterns".into(),
                            ),
                        },
                    );
                    docs!["wildcard: bitstring"]
                }
                PatKind::Error(_) => docs!["(* error *)"],
            }
        }

        fn expr(&self, expr: &Expr) -> DocBuilder<A> {
            // Mirrors `print#expr` (703-730), `print#expr'` (374-476), and
            // `print#expr_app` (357-372).
            match &*expr.kind {
                // ===== outer `expr` overrides (lines 703-730) =====
                ExprKind::App { head, args, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::into) =>
                {
                    // After Stage 2.0 the surface type of every value is
                    // `bitstring`, so `Into::into` is a no-op.
                    args.first().map(|a| docs![a]).unwrap_or(nil!())
                }
                ExprKind::App { head, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::never_to_any) =>
                {
                    docs!["bitstring_err()"]
                }

                // ===== Result-typed expressions (lines 712-730) =====
                ExprKind::Construct {
                    constructor,
                    fields,
                    ..
                } if *constructor == names::ResultOk => {
                    if let Some((_, inner)) = fields.first() {
                        docs![inner]
                    } else {
                        docs![""]
                    }
                }
                ExprKind::Construct { constructor, .. } if *constructor == names::ResultErr => {
                    docs!["bitstring_err()"]
                }

                // ===== expr' (lines 374-476) =====
                ExprKind::App { head, args, .. }
                    if matches!(&*head.kind, ExprKind::GlobalId(g)
                        if *g == names::clone || *g == names::unsize || *g == names::deref) =>
                {
                    // Identity passthrough (lines 386-405).
                    args.first().map(|a| docs![a]).unwrap_or(nil!())
                }
                ExprKind::App { head, args, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::logical_op_and) =>
                {
                    let lhs = args.first().map(|a| docs![a]).unwrap_or(nil!());
                    let rhs = args.get(1).map(|a| docs![a]).unwrap_or(nil!());
                    docs!["logical_and", paren_list!(vec![lhs, rhs])]
                }
                ExprKind::App { head, args, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::logical_op_or) =>
                {
                    let lhs = args.first().map(|a| docs![a]).unwrap_or(nil!());
                    let rhs = args.get(1).map(|a| docs![a]).unwrap_or(nil!());
                    docs!["logical_or", paren_list!(vec![lhs, rhs])]
                }
                ExprKind::App { head, args, .. } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::cast_op) =>
                {
                    // Cast → just the inner argument (line 401).
                    args.first().map(|a| docs![a]).unwrap_or(nil!())
                }

                // ===== Construct: Some / None / generic (lines 429-449) =====
                ExprKind::Construct { constructor, .. } if *constructor == names::OptionNone => {
                    docs!["None()"]
                }
                ExprKind::Construct {
                    constructor,
                    fields,
                    ..
                } if *constructor == names::OptionSome => {
                    if let Some((_, inner)) = fields.first() {
                        docs!["Some", docs![inner].parens()]
                    } else {
                        docs!["Some()"]
                    }
                }
                ExprKind::Construct {
                    constructor,
                    fields,
                    is_record,
                    is_struct: _,
                    base: _,
                } => {
                    // Mirrors `doc_construct_inductive` (lines 662-678).
                    if fields.is_empty() {
                        docs![constructor, "()"]
                    } else if *is_record {
                        let payload = comma_sep!(fields.iter().map(|(_, v)| docs![v]));
                        docs![constructor, paren_doc!(payload)]
                    } else {
                        let payload = comma_sep!(fields.iter().map(|(_, v)| docs![v]));
                        docs![constructor, paren_doc!(payload)]
                    }
                }

                // ===== Match → if-let chain (lines 450-456) =====
                //
                // ProVerif evaluates `letfun` bodies eagerly, so any
                // destructure that can fail must have an `else` clause —
                // otherwise the whole letfun call aborts, even from arms
                // that weren't taken. We therefore append a trailing
                // `else bitstring_err()` to the arm chain unless the last
                // arm itself already provides a fallback:
                //   - `PatKind::Wild` — the arm body is the fallback;
                //   - trivial binder (e.g. `Ok(x)` which strips to `x`) —
                //     the arm always succeeds, and ProVerif rejects `else`
                //     on a simple-binder `let` anyway;
                //   - `Result::Err(_)` — `match_arm` collapses this to
                //     `bitstring_err()` directly, which is itself a fallback.
                //
                // For (1) and (2), the arm absorbs all subsequent arms
                // (they're dynamically unreachable and ProVerif's grammar
                // can't express an `else` after such a `let`). Truncate
                // the arm list there.
                ExprKind::Match { scrutinee, arms } => {
                    let arm_always_matches = |arm: &Arm| -> bool {
                        matches!(*arm.pat.kind, PatKind::Wild) || Self::is_trivial_binder(&arm.pat)
                    };
                    let arm_is_result_err = |arm: &Arm| -> bool {
                        matches!(
                            &*arm.pat.kind,
                            PatKind::Construct { constructor, .. }
                                if *constructor == names::ResultErr
                        )
                    };
                    // ProVerif has no or-patterns. After
                    // `HoistDisjunctivePatterns` the alternatives sit at the top
                    // of the arm pattern, so split each `A | B => e` arm into one
                    // arm per alternative (sharing body + guard); the if-let chain
                    // below then renders one `let pat = scrutinee in body else ...`
                    // clause each.
                    let expanded: Vec<Arm> = arms
                        .iter()
                        .flat_map(|arm| match &*arm.pat.kind {
                            PatKind::Or { sub_pats } => sub_pats
                                .iter()
                                .map(|sp| Arm {
                                    pat: sp.clone(),
                                    body: arm.body.clone(),
                                    guard: arm.guard.clone(),
                                    meta: arm.meta.clone(),
                                })
                                .collect::<Vec<_>>(),
                            _ => vec![arm.clone()],
                        })
                        .collect();
                    // Take arms up to and including the first one that
                    // always matches.
                    let mut truncated: Vec<&Arm> = Vec::new();
                    for arm in expanded.iter() {
                        truncated.push(arm);
                        if arm_always_matches(arm) {
                            break;
                        }
                    }
                    let n_truncated = truncated.len();
                    let pieces: Vec<DocBuilder<A>> = truncated
                        .iter()
                        .enumerate()
                        .map(|(i, arm)| self.match_arm(scrutinee, arm, i + 1 == n_truncated))
                        .collect();
                    let chain = intersperse!(pieces, docs![hardline!(), "else "]);
                    let last_provides_fallback = truncated
                        .last()
                        .map(|arm| arm_always_matches(arm) || arm_is_result_err(arm))
                        .unwrap_or(false);
                    if last_provides_fallback {
                        chain
                    } else {
                        docs![chain, hardline!(), "else bitstring_err()"]
                    }
                }

                // ===== If / Let (lines 457-475) =====
                //
                // Stage 2.0: ProVerif's `if`/`then`/`else` requires a
                // `bool`-typed condition, but after the uniform-bitstring
                // collapse every condition is `bitstring`. Rewrite using
                // ProVerif's pattern-match let:
                //
                //   let (=True()) = cond in then_ else else_
                //
                // ProVerif treats a failing `let` pattern as taking the
                // `else` branch, exactly matching Rust's `if cond then ... else ...`.
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => match else_ {
                    Some(e) => docs![
                        "let (=True()) = ",
                        condition,
                        line!(),
                        "in ",
                        self.paren_unless_atomic(then),
                        line!(),
                        "else ",
                        self.paren_unless_atomic(e)
                    ]
                    .nest(INDENT)
                    .group(),
                    None => docs![
                        "let (=True()) = ",
                        condition,
                        line!(),
                        "in ",
                        self.paren_unless_atomic(then)
                    ]
                    .nest(INDENT)
                    .group(),
                },
                //
                // For a non-trivial (i.e., failable) pattern, ProVerif's
                // eager-evaluation semantics require an `else` clause —
                // otherwise a destructure that fails aborts the entire
                // letfun call (even if it's nested inside an unreached
                // Match arm). Wrap the body in parens so any `else` chain
                // *inside* `body` doesn't accidentally rebind to this
                // outer `let`. Trivial binders (`let x = e`) never fail
                // and ProVerif rejects an `else` clause on them, so we
                // emit them as-is.
                ExprKind::Let { lhs, rhs, body } => {
                    if Self::is_trivial_binder(lhs) {
                        docs![
                            "let ",
                            lhs,
                            " = ",
                            self.paren_unless_atomic(rhs),
                            " in",
                            hardline!(),
                            body
                        ]
                    } else {
                        docs![
                            "let ",
                            lhs,
                            " = ",
                            self.paren_unless_atomic(rhs),
                            " in ",
                            self.paren_unless_atomic(body),
                            " else bitstring_err()"
                        ]
                    }
                }

                // ===== expr_app fallback (357-372) =====
                ExprKind::App { head, args, .. } => {
                    let head_doc = docs![head];
                    if args.is_empty() {
                        docs![head_doc, "()"]
                    } else {
                        docs![head_doc, paren_list!(args.iter().map(|a| docs![a]))]
                    }
                }

                ExprKind::Literal(literal) => docs![literal],
                ExprKind::GlobalId(g) => docs![g],
                ExprKind::LocalId(local_id) => docs![local_id],
                ExprKind::Ascription { e, ty: _ } => docs![e],
                // ProVerif is first-order and has no array literals. Model a
                // fixed-size array `[a, b, c]` as a cons-list over the opaque
                // constructors `array_nil` / `array_cons` (declared in
                // `primitives.pvl`), i.e. `array_cons(a, array_cons(b,
                // array_cons(c, array_nil())))`. This is length-independent and
                // keeps everything within the uniform-bitstring encoding.
                // (Repeat arrays `[e; n]` never reach here — they are lowered
                // upstream to `rust_primitives::hax::repeat(e, n)`.)
                ExprKind::Array(elements) => elements.iter().rev().fold(
                    docs!["rust_primitives__hax__array_nil()"],
                    |rest, elem| {
                        docs![
                            "rust_primitives__hax__array_cons(",
                            docs![elem],
                            ", ",
                            rest,
                            ")"
                        ]
                    },
                ),
                ExprKind::Borrow { .. } => unreachable_by_invariant!(Drop_references),
                ExprKind::AddressOf { .. } => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                ExprKind::Assign { .. } => unreachable_by_invariant!(Local_mutation),
                // ProVerif has no loops. A `for`-loop over a collection —
                // which reaches the printer (post-`ReconstructForLoops` and
                // `LocalMutation`) as `LoopKind::ForLoop` with an explicit
                // functional `state` — is unrolled to a fixed `LOOP_BOUND`
                // depth by destructuring the iterator Seq (`array_cons` /
                // `array_nil` cons-list) one element at a time. All other
                // loop shapes (while, unconditional) reaching here without a
                // matching no-state arm below are still unsupported.
                ExprKind::Loop {
                    body,
                    kind,
                    state: Some(state),
                    ..
                } if matches!(&**kind, LoopKind::ForLoop { .. }) => {
                    let LoopKind::ForLoop { pat, iterator } = &**kind else {
                        unreachable!("guarded by the `matches!` above")
                    };
                    self.unroll_for_loop(pat, iterator, body, state)
                }
                // No-accumulator side-effecting `for x in coll { stmt }`
                // (`state: None`, unit body) — same `next()`-style unrolling
                // but with no threaded accumulator; the empty result is unit.
                ExprKind::Loop {
                    body,
                    kind,
                    state: None,
                    ..
                } if matches!(&**kind, LoopKind::ForLoop { .. }) => {
                    let LoopKind::ForLoop { pat, iterator } = &**kind else {
                        unreachable!("guarded by the `matches!` above")
                    };
                    self.unroll_for_loop_nostate(pat, iterator, body)
                }
                ExprKind::Loop { .. } => {
                    self.expr_error_placeholder::<A>("Loops not supported in ProVerif")
                }
                ExprKind::Break { .. } | ExprKind::Continue { .. } | ExprKind::Return { .. } => {
                    self.expr_error_placeholder::<A>(
                        "Early-exit control flow not supported in ProVerif",
                    )
                }
                ExprKind::Closure { .. } => {
                    self.expr_error_placeholder::<A>("Closures not supported in ProVerif")
                }
                ExprKind::Block { .. } => unreachable_by_invariant!(Drop_blocks),
                ExprKind::Quote { contents } => docs![contents],
                ExprKind::Resugared(_) => {
                    self.expr_error_placeholder::<A>("Unsupported resugared expression")
                }
                ExprKind::Error(e) => docs![e],
            }
        }

        fn arm(&self, _arm: &Arm) -> DocBuilder<A> {
            // Arms are emitted via `match_arm` (called from `expr`'s `Match`
            // branch); the bare default is unused.
            nil!()
        }

        fn param(&self, param: &Param) -> DocBuilder<A> {
            // Mirrors the `print#param` invocations sprinkled in
            // `item_unwrapped`: each parameter is `name: ty`.
            let name = match &*param.pat.kind {
                PatKind::Wild => text!("wildcard"),
                PatKind::Binding {
                    var,
                    mutable: false,
                    mode: BindingMode::ByValue,
                    sub_pat: None,
                } => docs![var],
                PatKind::Binding { var, .. } => docs![var],
                _ => docs![&param.pat],
            };
            docs![name, ": ", &param.ty]
        }

        fn variant(&self, variant: &Variant) -> DocBuilder<A> {
            // Used only when emitted directly; the actual struct/enum
            // constructor declarations come out of `fn item`.
            let args = comma_sep!(variant.arguments.iter().map(|(_, ty, _)| docs![ty]));
            docs![&variant.name, paren_doc!(args)]
        }

        fn item(&self, item: &Item) -> DocBuilder<A> {
            // Mirrors `print#item_unwrapped` (`proverif_backend.ml:480-642`).
            let attrs = &item.meta.attributes;
            let as_constructor = item
                .meta
                .hax_attributes()
                .any(|a| matches!(a, AttrPayload::PVConstructor));
            let as_handwritten = item
                .meta
                .hax_attributes()
                .any(|a| matches!(a, AttrPayload::PVHandwritten));
            let _is_process = item.meta.hax_attributes().any(|a| {
                matches!(
                    a,
                    AttrPayload::ProcessRead | AttrPayload::ProcessWrite | AttrPayload::ProcessInit
                )
            });
            let is_erased = item
                .meta
                .hax_attributes()
                .any(|a| matches!(a, AttrPayload::Erased));
            let _ = attrs;

            // Leading Rust doc comments → ProVerif `(* … *)`, but only for
            // items that actually emit something: an erased type / trait /
            // use / alias renders nothing, and a dangling comment would
            // visually attach to the *next* item.
            let renders_output = match item.kind() {
                ItemKind::Fn { .. } | ItemKind::Quote { .. } | ItemKind::Impl { .. } => true,
                ItemKind::Type { .. } => !is_erased,
                _ => false,
            };
            // Source-provenance comment for the items that carry a real def
            // span and a single name (Fn / Type); Impl methods get theirs in
            // `impl_item`.
            let src = if renders_output {
                match item.kind() {
                    ItemKind::Fn { name, .. } | ItemKind::Type { name, .. } => {
                        self.src_comment(item.meta.span, name)
                    }
                    _ => nil!(),
                }
            } else {
                nil!()
            };
            let leading_docs = if renders_output {
                docs![src, self.doc_comments(&item.meta.attributes)]
            } else {
                nil!()
            };

            let rendered = match item.kind() {
                ItemKind::Fn {
                    name, body, params, ..
                } => {
                    if params.is_empty() {
                        // Empty-param `fn`s are Rust consts. After Stage 2.0
                        // every value lives in `bitstring`.
                        docs!["const ", name, ": bitstring."]
                    } else if as_constructor || is_erased {
                        // `#[hax::proverif::constructor]` *and* `#[hax_lib::opaque]`
                        // both render as a free `[data]` constructor — symbolically
                        // an opaque function with no equations is exactly that:
                        // a fresh name with injective inputs. Without this,
                        // `opaque` would land here as a regular letfun with body
                        // `rust_primitives__hax__dropped_body`, which collides
                        // with any companion declaration that also names this
                        // function (e.g. a partner `proverif::replace(reduc ...)`).
                        let arg_types = comma_sep!(params.iter().map(|p| docs![&p.ty]));
                        let header = if is_erased && !as_constructor {
                            "(* opaque *)"
                        } else {
                            "(* marked as constructor *)"
                        };
                        docs![
                            header,
                            hardline!(),
                            "fun ",
                            name,
                            paren_doc!(arg_types),
                            ": bitstring [data]."
                        ]
                    } else if matches!(
                        &*body.kind,
                        ExprKind::App { head, .. }
                            if matches!(&*head.kind, ExprKind::GlobalId(g) if g == name)
                    ) {
                        // A letfun whose body is a call to itself (`f(..) = f(..)`)
                        // is a degenerate stub the frontend emits for an
                        // unresolvable external trait method (e.g. tls_codec's
                        // `Size::tls_serialized_len`). ProVerif forbids recursive
                        // letfuns, so emit an opaque `fun` instead — sound, since
                        // such serialization helpers are never security-relevant
                        // (the crypto boundary bypasses serialization).
                        let arg_types = comma_sep!(params.iter().map(|p| docs![&p.ty]));
                        docs![
                            "(* self-recursive stub (unresolved trait method) *)",
                            hardline!(),
                            "fun ",
                            name,
                            paren_doc!(arg_types),
                            ": bitstring."
                        ]
                    } else {
                        // Regular letfun (lines 560-588).
                        let comment = if as_handwritten {
                            docs!["(* REPLACE by handwritten model *)", hardline!()]
                        } else {
                            nil!()
                        };
                        let params_doc = comma_sep!(params.iter().map(|p| docs![p]));
                        let body_doc: DocBuilder<A> = if as_handwritten {
                            docs!["bitstring_default()"]
                        } else {
                            docs![body]
                        };
                        docs![
                            comment,
                            "letfun ",
                            name,
                            paren_doc!(params_doc),
                            " =",
                            docs![line!(), body_doc].nest(INDENT).group(),
                            "."
                        ]
                    }
                }

                ItemKind::Type {
                    name,
                    variants,
                    is_struct,
                    ..
                } => {
                    // Stage 2.0: emit only the `[data]` constructor and the
                    // per-field `reduc` accessors. The legacy type/converter/
                    // default/err cluster is replaced by the universal
                    // `bitstring_default`/`bitstring_err`/`Some`/`None` in the
                    // preamble.
                    if is_erased {
                        return nil!();
                    }
                    if *is_struct {
                        match variants.first() {
                            Some(v) => self.fun_and_reduc(name, v),
                            None => nil!(),
                        }
                    } else {
                        let pieces: Vec<DocBuilder<A>> = variants
                            .iter()
                            .map(|v| self.fun_and_reduc(name, v))
                            .collect();
                        intersperse!(pieces, hardline!())
                    }
                }

                ItemKind::Quote { quote, .. } => docs![quote],

                ItemKind::TyAlias { .. } => nil!(),
                ItemKind::Trait { .. } => nil!(),
                ItemKind::Impl { items, .. } => {
                    // Stage 2.1: render an impl block by flattening its
                    // items into top-level letfuns / consts. Specialize
                    // gave each impl item a unique flattened GlobalId
                    // (`<self_ty>__<trait>__<method>` for trait impls,
                    // `<self_ty>__<method>` for inherent impls), so we can
                    // emit them as ordinary items at the file level.
                    intersperse!(items.iter().map(|i| docs![i]), hardline!())
                }
                ItemKind::Alias { .. } => nil!(),
                ItemKind::Use { .. } | ItemKind::RustModule => nil!(),
                ItemKind::NotImplementedYet => nil!(),
                ItemKind::Resugared(_) => nil!(),
                ItemKind::Error(e) => docs![e],
            };
            // Annotate the rendered declaration (Fn / Type) with its source span
            // for the source map. Impl items are annotated individually in
            // `impl_item`; other kinds render nothing to map.
            let rendered = match item.kind() {
                ItemKind::Fn { .. } | ItemKind::Type { .. } if renders_output => {
                    Self::annotate_with_span(rendered, item.meta.span)
                }
                _ => rendered,
            };
            docs![leading_docs, rendered]
        }

        fn metadata(&self, _metadata: &Metadata) -> DocBuilder<A> {
            nil!()
        }

        fn attribute(&self, attribute: &Attribute) -> DocBuilder<A> {
            match &attribute.kind {
                AttributeKind::DocComment { body, .. } => {
                    docs!["(* ", body.clone(), " *)", hardline!()]
                }
                AttributeKind::Tool { .. } | AttributeKind::Hax(_) => nil!(),
            }
        }

        fn quote(&self, quote: &Quote) -> DocBuilder<A> {
            concat![&quote.0]
        }

        fn quote_content(&self, quote_content: &QuoteContent) -> DocBuilder<A> {
            match quote_content {
                QuoteContent::Verbatim(s) => {
                    intersperse!(s.lines().map(|x| x.to_string()), hardline!())
                }
                QuoteContent::Expr(e) => docs![e],
                QuoteContent::Pattern(p) => docs![p],
                QuoteContent::Ty(t) => docs![t],
            }
        }

        fn spanned_ty(&self, spanned_ty: &SpannedTy) -> DocBuilder<A> {
            docs![&spanned_ty.ty]
        }

        fn generics(&self, _generics: &Generics) -> DocBuilder<A> {
            nil!()
        }

        fn generic_param(&self, _generic_param: &GenericParam) -> DocBuilder<A> {
            nil!()
        }

        fn generic_constraint(&self, _gc: &GenericConstraint) -> DocBuilder<A> {
            nil!()
        }

        fn generic_value(&self, generic_value: &GenericValue) -> DocBuilder<A> {
            match generic_value {
                GenericValue::Ty(ty) => docs![ty],
                GenericValue::Expr(expr) => docs![expr],
                GenericValue::Lifetime => unreachable_by_invariant!(Drop_references),
            }
        }

        fn lhs(&self, _lhs: &Lhs) -> DocBuilder<A> {
            unreachable_by_invariant!(Local_mutation)
        }

        fn safety_kind(&self, _safety_kind: &SafetyKind) -> DocBuilder<A> {
            nil!()
        }

        fn region(&self, _region: &Region) -> DocBuilder<A> {
            unreachable_by_invariant!(Drop_references)
        }

        fn borrow_kind(&self, _borrow_kind: &BorrowKind) -> DocBuilder<A> {
            unreachable_by_invariant!(Drop_references)
        }

        fn binding_mode(&self, _binding_mode: &BindingMode) -> DocBuilder<A> {
            nil!()
        }

        fn guard(&self, _guard: &Guard) -> DocBuilder<A> {
            emit_error!("ProVerif backend does not support match guards")
        }

        fn dyn_trait_goal(&self, _: &DynTraitGoal) -> DocBuilder<A> {
            unreachable_by_invariant!(Reject_dyn)
        }

        fn impl_expr(&self, _impl_expr: &ImplExpr) -> DocBuilder<A> {
            nil!()
        }

        fn impl_ident(&self, _impl_ident: &ImplIdent) -> DocBuilder<A> {
            nil!()
        }

        fn trait_goal(&self, _trait_goal: &TraitGoal) -> DocBuilder<A> {
            nil!()
        }

        fn projection_predicate(&self, _: &ProjectionPredicate) -> DocBuilder<A> {
            nil!()
        }

        fn impl_item(&self, impl_item: &ImplItem) -> DocBuilder<A> {
            // Stage 2.1: render each impl item as a flat top-level
            // declaration. `Specialize` produces a unique `GlobalId` per
            // (impl, item) pair, so `impl_item.ident` already carries the
            // `<self_ty>__<trait>__<method>` flattened name we want.
            let name = self.render_id(&impl_item.ident);
            // Leading Rust doc comments on the method/const → ProVerif comments
            // (associated types emit nothing, so skip them to avoid a dangling
            // comment).
            let leading_docs = if matches!(&impl_item.kind, ImplItemKind::Type { .. }) {
                nil!()
            } else {
                docs![
                    self.src_comment(impl_item.meta.span, &impl_item.ident),
                    self.doc_comments(&impl_item.meta.attributes)
                ]
            };
            let rendered = match &impl_item.kind {
                // Associated types are bitstring; nothing to declare.
                ImplItemKind::Type { .. } => nil!(),
                ImplItemKind::Fn { body, params } => {
                    if params.is_empty() {
                        docs!["const ", name, ": bitstring."]
                    } else if matches!(
                        &*body.kind,
                        ExprKind::App { head, .. }
                            if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == impl_item.ident)
                    ) {
                        // `f(..) = f(..)` — a degenerate self-recursive stub for
                        // an unresolvable external trait method (e.g. tls_codec's
                        // `Size::tls_serialized_len`). ProVerif forbids recursive
                        // letfuns; emit an opaque `fun` instead (sound — these
                        // serialization helpers are never security-relevant).
                        let arg_types = comma_sep!(params.iter().map(|p| docs![&p.ty]));
                        docs![
                            "(* self-recursive stub (unresolved trait method) *)",
                            hardline!(),
                            "fun ",
                            name,
                            paren_doc!(arg_types),
                            ": bitstring."
                        ]
                    } else {
                        let params_doc = comma_sep!(params.iter().map(|p| docs![p]));
                        docs![
                            "letfun ",
                            name,
                            paren_doc!(params_doc),
                            " =",
                            docs![line!(), body].nest(INDENT).group(),
                            "."
                        ]
                    }
                }
                ImplItemKind::Resugared(ResugaredImplItemKind::Constant { body: _ }) => {
                    // Associated constants land as opaque `bitstring`. Users
                    // who care about the value can override with a verbatim
                    // `proverif_replace!` body.
                    docs!["const ", name, ": bitstring."]
                }
                ImplItemKind::Error(err) => docs![err],
            };
            docs![
                leading_docs,
                Self::annotate_with_span(rendered, impl_item.meta.span)
            ]
        }

        fn error_node(&self, _error_node: &ErrorNode) -> DocBuilder<A> {
            // ProVerif rejects bare comments in term position. `bitstring_err()`
            // is the universal "value we don't have" placeholder declared by
            // the preamble — keeping the surrounding letfun parseable while
            // still surfacing the failure via the trailing comment.
            docs!["bitstring_err()", " (* error node *)"]
        }
    }
};

// ===========================================================================
// Readability pass: SSA-freshen rebound local bindings.
//
// hax's `&mut` lowering + ANF threads state through a *chain* of `let`s that
// reuse the same name: `let self = … in … let self = … in …`. ProVerif
// tolerates this (letfun bodies allow shadowing) but warns `identifier self
// rebound` on every reuse, and the reader loses track of which `self` is the
// current one. This pass renames each successive rebinding to a fresh SSA name
// (`self`, `self_1`, `self_2`, …) and rewrites every later use to the latest
// version, turning the shadowed chain into a readable sequence that maps
// one-to-one onto the Rust mutation steps. It is a pure α-renaming —
// alpha-equivalent, so the model's meaning (and every verdict) is unchanged.
#[derive(Default)]
struct Freshen {
    /// Per-function map: rendered base name → number of bindings seen so far.
    /// Version 0 keeps the original name; version `v ≥ 1` renders `{base}_{v}`.
    counter: HashMap<String, usize>,
}

/// The `LocalId` bound by a simple (possibly ascribed) binding pattern, if any.
fn pat_binding_id(p: &Pat) -> Option<LocalId> {
    match &*p.kind {
        PatKind::Binding { var, .. } => Some(var.clone()),
        PatKind::Ascription { pat, .. } => pat_binding_id(pat),
        _ => None,
    }
}

impl Freshen {
    /// The rendered (ProVerif-escaped) base name of a local, mirroring
    /// `ProVerifPrinter::local_id` so rebind detection matches what ProVerif
    /// actually sees and generated suffixes render cleanly.
    fn base(id: &LocalId) -> String {
        let name = id.0.to_string();
        let rendered = if let Some(rest) = name.strip_prefix("impl ") {
            format!("impl_{}", rest.replace([' ', '+'], "_"))
        } else {
            name
        };
        ProVerifPrinter::escape(&rendered)
    }

    /// Allocate the SSA name for a freshly-bound variable. The first binding of
    /// a base name keeps the original `LocalId`; each subsequent (re)binding of
    /// a still-live name becomes `{base}_{v}`.
    fn alloc(&mut self, original: &LocalId) -> LocalId {
        let b = Self::base(original);
        let slot = self.counter.entry(b.clone()).or_insert(0);
        let cur = *slot;
        *slot += 1;
        if cur == 0 {
            original.clone()
        } else {
            LocalId(Symbol::new(format!("{b}_{cur}")))
        }
    }

    /// Entry point: SSA-freshen one top-level item.
    fn item(item: &mut Item) {
        match &mut item.kind {
            ItemKind::Fn { body, params, .. } => Self::function(params, body),
            ItemKind::Impl { items, .. } => {
                for ii in items.iter_mut() {
                    if let ImplItemKind::Fn { body, params } = &mut ii.kind {
                        Self::function(params, body);
                    }
                }
            }
            _ => {}
        }
    }

    /// Freshen one function body, seeding the scope with its parameters so the
    /// first `let self = …` in the body counts as a rebinding of the `self`
    /// parameter (yielding `self_1`).
    fn function(params: &[Param], body: &mut Expr) {
        let mut f = Freshen::default();
        let mut subst: HashMap<String, LocalId> = HashMap::new();
        for p in params {
            if let Some(id) = pat_binding_id(&p.pat) {
                let b = Self::base(&id);
                f.counter.insert(b.clone(), 1);
                subst.insert(b, id);
            }
        }
        f.expr(body, &subst);
    }

    /// `subst` maps a rendered base name to the `LocalId` that uses of that
    /// name currently resolve to. It is read-only here: scopes that introduce
    /// bindings (`let`/match-arm/closure/loop) build an extended *copy* and
    /// pass it down, so sibling branches never see each other's bindings. The
    /// version counter (`self.counter`) is intentionally shared across the
    /// whole function so suffixes stay globally unique.
    fn expr(&mut self, expr: &mut Expr, subst: &HashMap<String, LocalId>) {
        match &mut *expr.kind {
            ExprKind::LocalId(id) => {
                if let Some(cur) = subst.get(&Self::base(id)) {
                    *id = cur.clone();
                }
            }
            ExprKind::Let { lhs, rhs, body } => {
                // RHS is evaluated in the *outer* scope (before the binding).
                self.expr(rhs, subst);
                let mut inner = subst.clone();
                self.pat(lhs, &mut inner);
                self.expr(body, &inner);
            }
            ExprKind::App { head, args, .. } => {
                self.expr(head, subst);
                for a in args.iter_mut() {
                    self.expr(a, subst);
                }
            }
            ExprKind::Construct { fields, base, .. } => {
                for (_, v) in fields.iter_mut() {
                    self.expr(v, subst);
                }
                if let Some(b) = base {
                    self.expr(b, subst);
                }
            }
            ExprKind::Array(es) => {
                for e in es.iter_mut() {
                    self.expr(e, subst);
                }
            }
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                self.expr(condition, subst);
                self.expr(then, subst);
                if let Some(e) = else_ {
                    self.expr(e, subst);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee, subst);
                for arm in arms.iter_mut() {
                    let mut inner = subst.clone();
                    self.pat(&mut arm.pat, &mut inner);
                    if let Some(guard) = &mut arm.guard {
                        let GuardKind::IfLet { lhs, rhs } = &mut guard.kind;
                        // Guard RHS is in the arm's pre-guard scope; its
                        // pattern then binds into the arm body's scope.
                        self.expr(rhs, &inner);
                        self.pat(lhs, &mut inner);
                    }
                    self.expr(&mut arm.body, &inner);
                }
            }
            ExprKind::Ascription { e, .. } => self.expr(e, subst),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                for c in captures.iter_mut() {
                    self.expr(c, subst);
                }
                let mut inner = subst.clone();
                for p in params.iter_mut() {
                    self.pat(p, &mut inner);
                }
                self.expr(body, &inner);
            }
            ExprKind::Loop {
                body, kind, state, ..
            } => {
                let mut inner = subst.clone();
                match &mut **kind {
                    LoopKind::ForLoop { pat, iterator } => {
                        self.expr(iterator, subst);
                        self.pat(pat, &mut inner);
                    }
                    LoopKind::ForIndexLoop {
                        start, end, var, ..
                    } => {
                        self.expr(start, subst);
                        self.expr(end, subst);
                        let new = self.alloc(var);
                        inner.insert(Self::base(var), new.clone());
                        *var = new;
                    }
                    LoopKind::WhileLoop { condition } => self.expr(condition, &inner),
                    LoopKind::UnconditionalLoop => {}
                }
                if let Some(st) = state {
                    self.expr(&mut st.init, subst);
                    self.pat(&mut st.body_pat, &mut inner);
                }
                self.expr(body, &inner);
            }
            ExprKind::Borrow { inner, .. } | ExprKind::AddressOf { inner, .. } => {
                self.expr(inner, subst)
            }
            ExprKind::Block { body, .. } => self.expr(body, subst),
            ExprKind::Assign { value, .. } => self.expr(value, subst),
            ExprKind::Return { value } => self.expr(value, subst),
            ExprKind::Break { value, .. } => self.expr(value, subst),
            ExprKind::Continue { state, .. } => {
                if let Some(s) = state {
                    self.expr(s, subst);
                }
            }
            // Leaves and verbatim quotes (left untouched: a quote is
            // user-authored ProVerif that names its own variables).
            ExprKind::Literal(_)
            | ExprKind::GlobalId(_)
            | ExprKind::Quote { .. }
            | ExprKind::Resugared(_)
            | ExprKind::Error(_) => {}
        }
    }

    /// Allocate fresh SSA names for every binder in `pat`, recording each in
    /// `subst` so later uses resolve to it.
    fn pat(&mut self, pat: &mut Pat, subst: &mut HashMap<String, LocalId>) {
        match &mut *pat.kind {
            PatKind::Binding { var, sub_pat, .. } => {
                let new = self.alloc(var);
                subst.insert(Self::base(var), new.clone());
                *var = new;
                if let Some(sp) = sub_pat {
                    self.pat(sp, subst);
                }
            }
            PatKind::Construct { fields, .. } => {
                for (_, p) in fields.iter_mut() {
                    self.pat(p, subst);
                }
            }
            PatKind::Ascription { pat, .. } => self.pat(pat, subst),
            PatKind::Array { args } => {
                for p in args.iter_mut() {
                    self.pat(p, subst);
                }
            }
            PatKind::Deref { sub_pat } => self.pat(sub_pat, subst),
            PatKind::Or { sub_pats } => {
                // Or-alternatives bind the SAME variables; allocate from the
                // first and copy the mapping onto the rest so all alternatives
                // agree and the shared arm body sees one consistent name.
                if let Some((first, rest)) = sub_pats.split_first_mut() {
                    self.pat(first, subst);
                    for p in rest.iter_mut() {
                        Self::rebind_pat(p, subst);
                    }
                }
            }
            // `=lit` constant patterns and wildcards bind no nameable variable.
            PatKind::Constant { .. }
            | PatKind::Wild
            | PatKind::Resugared(_)
            | PatKind::Error(_) => {}
        }
    }

    /// Rename binders in `pat` to the names already chosen in `subst` (the
    /// non-first alternatives of an Or-pattern), without allocating new
    /// versions.
    fn rebind_pat(pat: &mut Pat, subst: &HashMap<String, LocalId>) {
        match &mut *pat.kind {
            PatKind::Binding { var, sub_pat, .. } => {
                if let Some(cur) = subst.get(&Self::base(var)) {
                    *var = cur.clone();
                }
                if let Some(sp) = sub_pat {
                    Self::rebind_pat(sp, subst);
                }
            }
            PatKind::Construct { fields, .. } => {
                for (_, p) in fields.iter_mut() {
                    Self::rebind_pat(p, subst);
                }
            }
            PatKind::Ascription { pat, .. } => Self::rebind_pat(pat, subst),
            PatKind::Array { args } => {
                for p in args.iter_mut() {
                    Self::rebind_pat(p, subst);
                }
            }
            PatKind::Deref { sub_pat } => Self::rebind_pat(sub_pat, subst),
            PatKind::Or { sub_pats } => {
                for p in sub_pats.iter_mut() {
                    Self::rebind_pat(p, subst);
                }
            }
            _ => {}
        }
    }
}

// ===========================================================================
// Readability pass: capture-avoiding inlining of single-use pure binders.
//
// ANF lowering introduces a flurry of throwaway aliases — `let hoist21 = out1
// in …`, `let hax_temp_output = C(…) in (…, hax_temp_output)` — that name a
// value used exactly once at the next step. Folding `let x = E in …x…` back to
// `…E…` removes that noise and brings the generated term close to the Rust
// expression it came from.
//
// Soundness. This runs AFTER the SSA-freshening pass, so every binder name in a
// function is unique — the "never inline E past a rebinding of E's free vars"
// and "never merge two live bindings" constraints are therefore automatic.
// What remains is ProVerif's *eager* `let`: `let x = E in body` evaluates E
// before `body`, so if E can fail, moving it into a conditionally-evaluated
// position would change when the failure happens. Hence:
//   * a total leaf (variable / global / literal) — which can never fail and has
//     no sub-evaluation — is inlined at its single use wherever that use is;
//   * any other atomic term (a function/constructor application) is inlined only
//     when its single use sits in an *unconditionally* evaluated position, so E
//     is evaluated exactly when it was before.
// Non-atomic E (a nested `let`/`if`/match) is never inlined — that keeps
// failable evaluation in place and avoids nesting a statement into an argument.
struct Inline;

/// The `LocalId` bound by a simple, infallible single-variable binder
/// (`let x = …`), peeling a type ascription. Tuple/`Some`/constructor
/// destructures and `x @ pat` are not simple binders and return `None`.
fn simple_binder(pat: &Pat) -> Option<LocalId> {
    match &*pat.kind {
        PatKind::Binding {
            var,
            sub_pat: None,
            mutable: false,
            mode: BindingMode::ByValue,
        } => Some(var.clone()),
        PatKind::Ascription { pat, .. } => simple_binder(pat),
        _ => None,
    }
}

/// A term that can never fail and carries no sub-evaluation: a local, a global,
/// or a literal (peeling ascriptions). Safe to inline into any position.
fn is_total_leaf(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::LocalId(_) | ExprKind::GlobalId(_) | ExprKind::Literal(_) => true,
        ExprKind::Ascription { e, .. } => is_total_leaf(e),
        _ => false,
    }
}

impl Inline {
    /// Entry point: inline within one top-level item.
    fn item(item: &mut Item) {
        match &mut item.kind {
            ItemKind::Fn { body, .. } => Self::go(body),
            ItemKind::Impl { items, .. } => {
                for ii in items.iter_mut() {
                    if let ImplItemKind::Fn { body, .. } = &mut ii.kind {
                        Self::go(body);
                    }
                }
            }
            _ => {}
        }
    }

    /// Inline bottom-up: fold inlinable lets inside the children first (so a use
    /// count is final by the time the enclosing let is considered), then fold
    /// this node if it is an inlinable `let`.
    fn go(expr: &mut Expr) {
        Self::recurse(expr);
        let folded = if let ExprKind::Let { lhs, rhs, body } = &*expr.kind {
            match simple_binder(lhs) {
                Some(x) => {
                    let (count, in_quote) = count_uses(body, &x);
                    let safe = count == 1
                        && !in_quote
                        && (is_total_leaf(rhs)
                            || (ProVerifPrinter::expr_is_atomic(rhs) && uncond_use(body, &x)));
                    if safe {
                        let mut new_body = body.clone();
                        subst_once(&mut new_body, &x, rhs);
                        Some(new_body)
                    } else {
                        None
                    }
                }
                None => None,
            }
        } else {
            None
        };
        if let Some(nb) = folded {
            *expr = nb;
        }
    }

    /// Recurse `go` into every sub-expression (all positions; quotes are left
    /// untouched — a quote is verbatim ProVerif naming its own variables).
    fn recurse(expr: &mut Expr) {
        match &mut *expr.kind {
            ExprKind::Let { rhs, body, .. } => {
                Self::go(rhs);
                Self::go(body);
            }
            ExprKind::App { head, args, .. } => {
                Self::go(head);
                for a in args.iter_mut() {
                    Self::go(a);
                }
            }
            ExprKind::Construct { fields, base, .. } => {
                for (_, v) in fields.iter_mut() {
                    Self::go(v);
                }
                if let Some(b) = base {
                    Self::go(b);
                }
            }
            ExprKind::Array(es) => {
                for e in es.iter_mut() {
                    Self::go(e);
                }
            }
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                Self::go(condition);
                Self::go(then);
                if let Some(e) = else_ {
                    Self::go(e);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                Self::go(scrutinee);
                for arm in arms.iter_mut() {
                    if let Some(g) = &mut arm.guard {
                        let GuardKind::IfLet { rhs, .. } = &mut g.kind;
                        Self::go(rhs);
                    }
                    Self::go(&mut arm.body);
                }
            }
            ExprKind::Ascription { e, .. } => Self::go(e),
            ExprKind::Closure { body, captures, .. } => {
                for c in captures.iter_mut() {
                    Self::go(c);
                }
                Self::go(body);
            }
            ExprKind::Loop {
                body, kind, state, ..
            } => {
                match &mut **kind {
                    LoopKind::ForLoop { iterator, .. } => Self::go(iterator),
                    LoopKind::ForIndexLoop { start, end, .. } => {
                        Self::go(start);
                        Self::go(end);
                    }
                    LoopKind::WhileLoop { condition } => Self::go(condition),
                    LoopKind::UnconditionalLoop => {}
                }
                if let Some(st) = state {
                    Self::go(&mut st.init);
                }
                Self::go(body);
            }
            ExprKind::Borrow { inner, .. } | ExprKind::AddressOf { inner, .. } => Self::go(inner),
            ExprKind::Block { body, .. } => Self::go(body),
            ExprKind::Assign { value, .. } => Self::go(value),
            ExprKind::Return { value } => Self::go(value),
            ExprKind::Break { value, .. } => Self::go(value),
            ExprKind::Continue { state, .. } => {
                if let Some(s) = state {
                    Self::go(s);
                }
            }
            ExprKind::Literal(_)
            | ExprKind::GlobalId(_)
            | ExprKind::LocalId(_)
            | ExprKind::Quote { .. }
            | ExprKind::Resugared(_)
            | ExprKind::Error(_) => {}
        }
    }
}

/// Count free uses of `x` in `e` (by exact `LocalId`), and report whether any
/// occurrence sits inside a verbatim quote. A quote occurrence makes `x`
/// ineligible for inlining: the substitution does not rewrite quote interiors,
/// so dropping the `let` would leave a dangling reference. Over-counting is
/// safe (we only inline at count 1); we never under-count.
fn count_uses(e: &Expr, x: &LocalId) -> (usize, bool) {
    let mut n = 0usize;
    let mut in_quote = false;
    count_uses_rec(e, x, &mut n, &mut in_quote);
    (n, in_quote)
}

fn count_uses_rec(e: &Expr, x: &LocalId, n: &mut usize, in_quote: &mut bool) {
    match &*e.kind {
        ExprKind::LocalId(id) => {
            if id == x {
                *n += 1;
            }
        }
        ExprKind::Quote { .. } => {
            // We never substitute into a verbatim quote; conservatively treat
            // any quote in the binder's scope as making it ineligible (the ANF
            // let-chains we inline never contain quotes, so no real target is
            // lost). Avoids leaving a dangling reference if the quote uses `x`.
            *in_quote = true;
        }
        ExprKind::Let { rhs, body, .. } => {
            count_uses_rec(rhs, x, n, in_quote);
            count_uses_rec(body, x, n, in_quote);
        }
        ExprKind::App { head, args, .. } => {
            count_uses_rec(head, x, n, in_quote);
            for a in args {
                count_uses_rec(a, x, n, in_quote);
            }
        }
        ExprKind::Construct { fields, base, .. } => {
            for (_, v) in fields {
                count_uses_rec(v, x, n, in_quote);
            }
            if let Some(b) = base {
                count_uses_rec(b, x, n, in_quote);
            }
        }
        ExprKind::Array(es) => {
            for e in es {
                count_uses_rec(e, x, n, in_quote);
            }
        }
        ExprKind::If {
            condition,
            then,
            else_,
        } => {
            count_uses_rec(condition, x, n, in_quote);
            count_uses_rec(then, x, n, in_quote);
            if let Some(e) = else_ {
                count_uses_rec(e, x, n, in_quote);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            count_uses_rec(scrutinee, x, n, in_quote);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    let GuardKind::IfLet { rhs, .. } = &g.kind;
                    count_uses_rec(rhs, x, n, in_quote);
                }
                count_uses_rec(&arm.body, x, n, in_quote);
            }
        }
        ExprKind::Ascription { e, .. } => count_uses_rec(e, x, n, in_quote),
        ExprKind::Closure { body, captures, .. } => {
            for c in captures {
                count_uses_rec(c, x, n, in_quote);
            }
            count_uses_rec(body, x, n, in_quote);
        }
        ExprKind::Loop {
            body, kind, state, ..
        } => {
            match &**kind {
                LoopKind::ForLoop { iterator, .. } => count_uses_rec(iterator, x, n, in_quote),
                LoopKind::ForIndexLoop { start, end, .. } => {
                    count_uses_rec(start, x, n, in_quote);
                    count_uses_rec(end, x, n, in_quote);
                }
                LoopKind::WhileLoop { condition } => count_uses_rec(condition, x, n, in_quote),
                LoopKind::UnconditionalLoop => {}
            }
            if let Some(st) = state {
                count_uses_rec(&st.init, x, n, in_quote);
            }
            count_uses_rec(body, x, n, in_quote);
        }
        ExprKind::Borrow { inner, .. } | ExprKind::AddressOf { inner, .. } => {
            count_uses_rec(inner, x, n, in_quote)
        }
        ExprKind::Block { body, .. } => count_uses_rec(body, x, n, in_quote),
        ExprKind::Assign { value, .. } => count_uses_rec(value, x, n, in_quote),
        ExprKind::Return { value } => count_uses_rec(value, x, n, in_quote),
        ExprKind::Break { value, .. } => count_uses_rec(value, x, n, in_quote),
        ExprKind::Continue { state, .. } => {
            if let Some(s) = state {
                count_uses_rec(s, x, n, in_quote);
            }
        }
        ExprKind::Literal(_)
        | ExprKind::GlobalId(_)
        | ExprKind::Resugared(_)
        | ExprKind::Error(_) => {}
    }
}

/// Whether the single occurrence of `x` in `e` sits in an *unconditionally*
/// evaluated position — i.e. it is reached without first passing through an
/// `if`/match arm, closure, or loop body. Only the always-evaluated parts of
/// each node are descended (a `let`'s rhs and body; every argument of an
/// application; an `if`/match scrutinee/condition).
fn uncond_use(e: &Expr, x: &LocalId) -> bool {
    match &*e.kind {
        ExprKind::LocalId(id) => id == x,
        ExprKind::Let { rhs, body, .. } => uncond_use(rhs, x) || uncond_use(body, x),
        ExprKind::App { head, args, .. } => {
            uncond_use(head, x) || args.iter().any(|a| uncond_use(a, x))
        }
        ExprKind::Construct { fields, base, .. } => {
            fields.iter().any(|(_, v)| uncond_use(v, x))
                || base.as_ref().is_some_and(|b| uncond_use(b, x))
        }
        ExprKind::Array(es) => es.iter().any(|e| uncond_use(e, x)),
        ExprKind::Ascription { e, .. } => uncond_use(e, x),
        // Only the condition / scrutinee is unconditional; branches are not.
        ExprKind::If { condition, .. } => uncond_use(condition, x),
        ExprKind::Match { scrutinee, .. } => uncond_use(scrutinee, x),
        ExprKind::Borrow { inner, .. } | ExprKind::AddressOf { inner, .. } => uncond_use(inner, x),
        ExprKind::Block { body, .. } => uncond_use(body, x),
        ExprKind::Return { value } => uncond_use(value, x),
        // Closures / loops defer evaluation; everything else is a leaf.
        _ => false,
    }
}

/// Replace each free `LocalId(x)` in `e` with a clone of `replacement`. After
/// SSA there is exactly one such occurrence; quotes are not descended.
fn subst_once(e: &mut Expr, x: &LocalId, replacement: &Expr) {
    match &mut *e.kind {
        ExprKind::LocalId(id) => {
            if id == x {
                *e = replacement.clone();
            }
        }
        ExprKind::Quote { .. } => {}
        ExprKind::Let { rhs, body, .. } => {
            subst_once(rhs, x, replacement);
            subst_once(body, x, replacement);
        }
        ExprKind::App { head, args, .. } => {
            subst_once(head, x, replacement);
            for a in args.iter_mut() {
                subst_once(a, x, replacement);
            }
        }
        ExprKind::Construct { fields, base, .. } => {
            for (_, v) in fields.iter_mut() {
                subst_once(v, x, replacement);
            }
            if let Some(b) = base {
                subst_once(b, x, replacement);
            }
        }
        ExprKind::Array(es) => {
            for e in es.iter_mut() {
                subst_once(e, x, replacement);
            }
        }
        ExprKind::If {
            condition,
            then,
            else_,
        } => {
            subst_once(condition, x, replacement);
            subst_once(then, x, replacement);
            if let Some(e) = else_ {
                subst_once(e, x, replacement);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            subst_once(scrutinee, x, replacement);
            for arm in arms.iter_mut() {
                if let Some(g) = &mut arm.guard {
                    let GuardKind::IfLet { rhs, .. } = &mut g.kind;
                    subst_once(rhs, x, replacement);
                }
                subst_once(&mut arm.body, x, replacement);
            }
        }
        ExprKind::Ascription { e, .. } => subst_once(e, x, replacement),
        ExprKind::Closure { body, captures, .. } => {
            for c in captures.iter_mut() {
                subst_once(c, x, replacement);
            }
            subst_once(body, x, replacement);
        }
        ExprKind::Loop {
            body, kind, state, ..
        } => {
            match &mut **kind {
                LoopKind::ForLoop { iterator, .. } => subst_once(iterator, x, replacement),
                LoopKind::ForIndexLoop { start, end, .. } => {
                    subst_once(start, x, replacement);
                    subst_once(end, x, replacement);
                }
                LoopKind::WhileLoop { condition } => subst_once(condition, x, replacement),
                LoopKind::UnconditionalLoop => {}
            }
            if let Some(st) = state {
                subst_once(&mut st.init, x, replacement);
            }
            subst_once(body, x, replacement);
        }
        ExprKind::Borrow { inner, .. } | ExprKind::AddressOf { inner, .. } => {
            subst_once(inner, x, replacement)
        }
        ExprKind::Block { body, .. } => subst_once(body, x, replacement),
        ExprKind::Assign { value, .. } => subst_once(value, x, replacement),
        ExprKind::Return { value } => subst_once(value, x, replacement),
        ExprKind::Break { value, .. } => subst_once(value, x, replacement),
        ExprKind::Continue { state, .. } => {
            if let Some(s) = state {
                subst_once(s, x, replacement);
            }
        }
        ExprKind::Literal(_)
        | ExprKind::GlobalId(_)
        | ExprKind::Resugared(_)
        | ExprKind::Error(_) => {}
    }
}

/// The ProVerif backend.
pub struct ProVerifBackend;

impl Backend for ProVerifBackend {
    type Printer = ProVerifPrinter;

    /// Single-file output (`lib.pvl`) — matches the legacy OCaml backend's
    /// behaviour (see `proverif_backend.ml:868-881`).
    fn module_path(&self, _module: &Module) -> Utf8PathBuf {
        Utf8PathBuf::from("lib.pvl")
    }

    /// The phase pipeline. Stage 2.1 inserts `Specialize` between
    /// `TransformHaxLibInline` and the rest — same shape Lean / F\* use —
    /// so trait method calls are monomorphized into concrete
    /// `<self_ty>__<trait>__<method>` letfun calls before the printer runs.
    fn phases(&self) -> Vec<PhaseKind> {
        use crate::phase::{PhaseKind::*, legacy::LegacyOCamlPhase::*};
        vec![
            RejectUnsafe.into(),
            RejectRawOrMutPointer.into(),
            TransformHaxLibInline.into(),
            Specialize.into(),
            SimplifyQuestionMarks.into(),
            AndMutDefsite.into(),
            ReconstructForLoops.into(),
            DirectAndMut.into(),
            RejectArbitraryLhs.into(),
            DropBlocks.into(),
            DropReferences.into(),
            TrivializeAssignLhs.into(),
            HoistSideEffects.into(),
            // Expand or-patterns (`A | B => e`) into one arm per constructor,
            // like the F* and Lean backends — ProVerif has no or-patterns, and
            // without this the printer hits them and emits a HAX0001 error.
            HoistDisjunctivePatterns.into(),
            SimplifyMatchReturn.into(),
            // `LocalMutation` must run *before* the control-flow phases below.
            // It is what threads a loop's mutable state into the `Loop` /
            // `Break` / `Continue` nodes (`LoopState`), and
            // `DropReturnBreakContinue` needs that state to encode `break` /
            // `continue` into the `ControlFlow` enum. Ordered after them, those
            // nodes instead survive into `dexpr'` and raise the HAX0002
            // "Return/Break/Continue are expected to be gone as this point"
            // fatal. Both the F* pipeline and the legacy OCaml ProVerif backend
            // run it directly after `SimplifyMatchReturn`.
            LocalMutation.into(),
            // Functionalize early-exit control flow (`return`/`break`/`continue`)
            // into if/match, like the F* backend — otherwise `if c { ...; return }`
            // / `let-else { ...; return }` reach the printer as unsupported
            // `ExprKind::Return`.
            RewriteControlFlow.into(),
            DropReturnBreakContinue.into(),
            RejectContinue.into(),
            RejectDyn.into(),
            ReorderFields.into(),
            BundleCycles.into(),
            SortItemsNamespaceWise.into(),
            ProverifCombinatorsToLoops,
            ProverifResolveTraitCalls,
            ProverifExpandStructUpdate,
            FilterUnprintableItems,
        ]
    }

    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        // Stage 2.2: `#[hax_lib::pv_inline]` β-substitution. Two phases
        // sharing a state: first collects inlinable items, then rewrites
        // call sites and marks the originals late-skip.
        use crate::resugarings::pv_inline_resugarings;
        pv_inline_resugarings()
    }

    /// Collapse every module into a single bag of items so the printer emits
    /// one `lib.pvl` file. Matches `proverif_backend.ml:868-881`.
    fn items_to_module(&self, items: Vec<Item>) -> Vec<Module> {
        if items.is_empty() {
            return vec![];
        }
        let module_ident = items[0].ident.mod_only_closest_parent();
        vec![Module {
            ident: module_ident,
            items,
            meta: Metadata {
                span: Span::dummy(),
                attributes: vec![],
            },
        }]
    }

    fn modules_to_files(&self, mut modules: Vec<Module>, mut printer: Self::Printer) -> Vec<File> {
        if modules.is_empty() {
            return vec![];
        }
        // Readability pass: SSA-freshen rebound local bindings so the
        // generated model reads as a sequence of distinct state versions
        // (`self`, `self_1`, …) instead of a shadowed chain, and ProVerif
        // stops warning `identifier X rebound`. Pure α-renaming.
        for module in &mut modules {
            for item in &mut module.items {
                Freshen::item(item);
                // Inline single-use pure binders (the SSA pass above first makes
                // every binder unique, so this inlining is capture-free).
                Inline::item(item);
            }
        }
        let path = self.module_path(modules.first().unwrap()).to_string();
        // Pre-compute the set of const-generic `LocalId`s that the
        // printer should treat as "erased" — those names show up in
        // expression position whenever a generic function references
        // `N` from `[T; N]` or similar, and ProVerif has no notion of
        // a free type/const parameter standing in for a runtime value.
        // The surrounding type collapses to `bitstring` anyway, so the
        // value is symbolically irrelevant; we render any such ref as
        // `bitstring_default()`.
        for module in &modules {
            for item in &module.items {
                collect_erased_const_generics(item, &mut printer.erased_const_generics);
            }
        }
        // Collect every `GlobalId` referenced in expression / pattern
        // position from the AST.
        let referenced = collect_references(&modules, &mut printer);
        // Render the body, harvesting per-item source-span anchors as we go so
        // we can emit a v3 source map alongside `lib.pvl`. `render_with_span_
        // positions` produces text byte-identical to `printer.print(..)` (the
        // span annotations are zero-width) plus the output `(line, col, span)`
        // of each annotated item.
        let mut parts: Vec<String> = Vec::new();
        let mut positions: Vec<(usize, usize, Span)> = Vec::new();
        let mut line_base = 0usize;
        for module in modules.into_iter() {
            let (text, pos) =
                render_with_span_positions(&printer, module, ProVerifPrinter::RENDER_WIDTH);
            for (l, c, span) in pos {
                positions.push((l + line_base, c, span));
            }
            // Modules are joined by a single "\n" below.
            line_base += text.matches('\n').count() + 1;
            parts.push(text);
        }
        let contents = parts.join("\n");
        // Scan the rendered body for the names it already declares
        // (including ones synthesized by `proverif_replace_body!`
        // quote injections such as `reduc forall ...; foo(...) = ...`),
        // then emit an auto-decl block only for what's still missing.
        // The auto-declared externals go to a SEPARATE `missingdecl.pvl`
        // diagnostic file rather than being silently inlined into lib.pvl,
        // so the unsound stubs are visible and auditable (goal: empty).
        let missingdecl = self.format_external_decls(&referenced, &contents);
        // The body is prepended with `HEADER`, so shift the harvested generated
        // line numbers down by the preamble's line count before building the map.
        let header_lines = HEADER.matches('\n').count();
        let sourcemap = build_source_map(&path, header_lines, &positions);
        vec![
            File {
                contents: format!("{HEADER}{contents}"),
                sourcemap,
                path,
            },
            File {
                path: "missingdecl.pvl".to_string(),
                contents: missingdecl,
                sourcemap: None,
            },
        ]
    }
}

fn collect_erased_const_generics(item: &Item, out: &mut HashSet<LocalId>) {
    let generics = match item.kind() {
        ItemKind::Fn { generics, .. }
        | ItemKind::Impl { generics, .. }
        | ItemKind::Trait { generics, .. }
        | ItemKind::Type { generics, .. } => Some(generics),
        _ => None,
    };
    if let Some(g) = generics {
        for p in &g.params {
            if matches!(p.kind, GenericParamKind::Const { .. }) {
                out.insert(p.ident.clone());
            }
        }
    }
    if let ItemKind::Impl { items, .. } = item.kind() {
        for ii in items {
            for p in &ii.generics.params {
                if matches!(p.kind, GenericParamKind::Const { .. }) {
                    out.insert(p.ident.clone());
                }
            }
        }
    }
}

/// Per-reference info kept while scanning the AST. Tracks max-observed
/// arity at use sites and whether the symbol appears in `Construct` /
/// `PatKind::Construct` position (in which case it must be declared
/// `[data]`).
struct RefInfo {
    arity: usize,
    is_constructor: bool,
}

/// Walk every `Module` and produce a `name → RefInfo` map of every
/// `GlobalId` referenced in expression or pattern position. The names
/// are rendered as strings (ProVerif has one global namespace, so two
/// `GlobalId`s that share a rendered name are the same identifier).
fn collect_references(
    modules: &[Module],
    printer: &mut ProVerifPrinter,
) -> HashMap<String, RefInfo> {
    let mut referenced: HashMap<String, RefInfo> = HashMap::new();
    for module in modules {
        for item in &module.items {
            let mut v = ExternRefCollector::default();
            v.visit_item(item);
            for r in v.calls {
                let name = printer.render_id(&r.id);
                let info = referenced.entry(name).or_insert(RefInfo {
                    arity: 0,
                    is_constructor: false,
                });
                info.arity = info.arity.max(r.arity);
                info.is_constructor |= r.is_constructor;
            }
            for name in v.lit_consts {
                referenced.entry(name).or_insert(RefInfo {
                    arity: 0,
                    is_constructor: false,
                });
            }
        }
    }
    referenced
}

impl ProVerifBackend {
    /// Emit the auto-declared-externals block for the file.
    ///
    /// A name in `referenced` is "external" (and needs a declaration)
    /// unless it's already declared by one of:
    ///  - the HEADER preamble (built-ins like `Some`, `True`, …);
    ///  - the bundled `primitives.pvl` library (run ProVerif with
    ///    `-lib primitives.pvl`);
    ///  - the *rendered* `rendered` body — picks up `letfun`, `fun [data]`,
    ///    `const`, and (importantly) `reduc forall ...; F(...) = ...`
    ///    declarations introduced by `proverif_replace!` /
    ///    `proverif_before!` quote injections.
    fn format_external_decls(
        &self,
        referenced: &HashMap<String, RefInfo>,
        rendered: &str,
    ) -> String {
        let mut defined: HashSet<String> = HashSet::new();
        for s in [
            "construct_fail",
            "empty",
            "bitstring_default",
            "bitstring_err",
            "Some",
            "None",
            "Option_err",
            "True",
            "False",
            "bool_default",
            "bool_err",
            "nat_lit",
            "logical_and",
            "logical_or",
        ] {
            defined.insert(s.to_string());
        }
        for name in primitives_pvl_names() {
            defined.insert(name);
        }
        for name in scan_declared_names(rendered) {
            defined.insert(name);
        }

        let mut decls: Vec<String> = Vec::new();
        let mut keys: Vec<String> = referenced
            .keys()
            .filter(|k| !defined.contains(k.as_str()))
            .cloned()
            .collect();
        keys.sort();
        for name in keys {
            let info = &referenced[&name];
            if info.arity == 0 {
                decls.push(format!("const {name}: bitstring."));
            } else {
                let args = std::iter::repeat_n("bitstring", info.arity)
                    .collect::<Vec<_>>()
                    .join(", ");
                // NO `[data]`: these are placeholders for symbols we have
                // no definition for, so we don't know their real nature
                // (one-way `fun`, data constructor, or `letfun` with
                // equations). `missingdecl.pvl` is a diagnostic, not part
                // of the model — every entry is meant to be replaced by a
                // real definition (by hand, or from another crate's
                // extraction) — so we must NOT presume the invertible
                // `[data]` form, which would let an attacker recover a
                // one-way function's inputs.
                decls.push(format!("fun {name}({args}): bitstring."));
            }
        }
        let body = if decls.is_empty() {
            "(* (none — every referenced symbol is defined in lib.pvl, *)\n\
             (* primitives.pvl, or a -lib'd dependency.)               *)"
                .to_string()
        } else {
            decls.join("\n")
        };
        format!(
            "(*****************************************************************)\n\
             (* missingdecl.pvl — UNDEFINED externals referenced by lib.pvl   *)\n\
             (*                                                               *)\n\
             (* DIAGNOSTIC, not part of the model. Each symbol below is       *)\n\
             (* referenced by lib.pvl but has no definition (and is not in    *)\n\
             (* primitives.pvl). Supply a real one by hand, or by extracting  *)\n\
             (* the crate that owns it (e.g. a separately-extracted           *)\n\
             (* dependency). Declared WITHOUT `[data]` because the real       *)\n\
             (* nature (one-way fun / data constructor / letfun) is unknown.  *)\n\
             (* GOAL: this file is EMPTY.                                     *)\n\
             (*****************************************************************)\n\
             {body}\n"
        )
    }
}

/// Scan rendered `.pvl` text and return every name introduced by a
/// `fun`, `letfun`, `const`, or `reduc forall ...; <name>(...)` line.
/// Used by the auto-decl pass to avoid redeclaring identifiers that
/// the printer has *already* emitted — including those synthesised by
/// `proverif_replace!` / `proverif_before!` quote injections that
/// inline raw ProVerif syntax.
fn scan_declared_names(rendered: &str) -> Vec<String> {
    /// State machine: a `reduc forall ...;` header can:
    ///  - finish on the same line: `reduc forall b1, b2; F(args) = ...`
    ///  - wrap so `;` lands later but with the destructor name on the
    ///    same line: `reduc forall <multiline>; F(args) = ...`
    ///  - wrap further so the destructor name is on yet another line:
    ///
    /// ```text
    /// reduc forall
    ///   b1: t1,
    ///   b2: t2;
    ///
    ///   F(args)
    ///   = ...
    /// ```
    ///
    /// We need to pick up `F` in all three shapes.
    enum ReducState {
        None,
        SeenReduc,    // saw bare `reduc`, waiting for `forall`
        SeenHeader,   // saw `reduc forall`, waiting for `;`
        AwaitingHead, // saw `;`, looking for the next non-empty token
    }
    let mut out: Vec<String> = Vec::new();
    let mut state = ReducState::None;
    for line in rendered.lines() {
        let s = line.trim_start();
        // `fun NAME(...)`, `letfun NAME(...)`, `const NAME: ...`
        for kw in ["fun ", "letfun ", "const "] {
            if let Some(rest) = s.strip_prefix(kw) {
                let end = rest.find(['(', ':', ' ', '\t']).unwrap_or(rest.len());
                let name = rest[..end].trim();
                if !name.is_empty() {
                    out.push(name.to_string());
                }
            }
        }

        // Strip `reduc forall` followed by either a space or end-of-line.
        let reduc_after: Option<&str> = s
            .strip_prefix("reduc forall ")
            .or_else(|| s.strip_prefix("reduc forall").map(str::trim_start))
            .filter(|_| {
                s == "reduc forall"
                    || s.starts_with("reduc forall ")
                    || s.starts_with("reduc forall\t")
            });
        match state {
            ReducState::None => {
                if let Some(after) = reduc_after {
                    if let Some((_, tail)) = after.split_once(';') {
                        if let Some(name) = extract_call_head(tail) {
                            out.push(name);
                            state = ReducState::None;
                        } else {
                            state = ReducState::AwaitingHead;
                        }
                    } else {
                        state = ReducState::SeenHeader;
                    }
                } else if s == "reduc" {
                    state = ReducState::SeenReduc;
                }
            }
            ReducState::SeenReduc => {
                if s.starts_with("forall") {
                    if let Some((_, tail)) = s.split_once(';') {
                        if let Some(name) = extract_call_head(tail) {
                            out.push(name);
                            state = ReducState::None;
                        } else {
                            state = ReducState::AwaitingHead;
                        }
                    } else {
                        state = ReducState::SeenHeader;
                    }
                }
            }
            ReducState::SeenHeader => {
                if let Some((_, after)) = s.split_once(';') {
                    if let Some(name) = extract_call_head(after) {
                        out.push(name);
                        state = ReducState::None;
                    } else {
                        state = ReducState::AwaitingHead;
                    }
                }
            }
            ReducState::AwaitingHead => {
                if s.is_empty() {
                    continue;
                }
                if let Some(name) = extract_call_head(s) {
                    out.push(name);
                }
                state = ReducState::None;
            }
        }
    }
    out
}

fn extract_call_head(text: &str) -> Option<String> {
    let t = text.trim_start();
    let end = t.find(|c: char| c == '(' || c.is_whitespace())?;
    let name = t[..end].trim();
    (!name.is_empty()).then(|| name.to_string())
}

/// Turn a string / char / float-literal value into a valid ProVerif
/// identifier suffix. Replaces every non-`[A-Za-z0-9_]` byte with
/// `_xHH` (two-hex), so the mapping is injective (distinct literals →
/// distinct identifiers). Empty input yields `empty`.
fn sanitize_string_literal(s: &str) -> String {
    if s.is_empty() {
        return "empty".to_string();
    }
    let mut out = String::with_capacity(s.len());
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || b == b'_' {
            out.push(b as char);
        } else {
            out.push_str(&format!("_x{b:02x}"));
        }
    }
    out
}

/// Parse `PRIMITIVES_PVL` once and return the set of `fun NAME(...)`,
/// `const NAME: ...`, and `reduc forall ...; accessor_NAME(...)` declarations.
/// We use a simple regex-free scan: any token at the start of a line
/// after `fun` / `const` / `letfun` (before its `(` or `:` separator).
fn primitives_pvl_names() -> Vec<String> {
    static NAMES: OnceLock<Vec<String>> = OnceLock::new();
    NAMES
        .get_or_init(|| {
            let mut out: Vec<String> = Vec::new();
            for line in PRIMITIVES_PVL.lines() {
                let line = line.trim_start();
                let head = if let Some(rest) = line.strip_prefix("fun ") {
                    rest
                } else if let Some(rest) = line.strip_prefix("const ") {
                    rest
                } else if let Some(rest) = line.strip_prefix("letfun ") {
                    rest
                } else {
                    continue;
                };
                // Identifier ends at first `(`, `:`, ` `, or end-of-line.
                let end = head.find(['(', ':', ' ']).unwrap_or(head.len());
                let name = head[..end].trim();
                if !name.is_empty() {
                    out.push(name.to_string());
                }
            }
            out
        })
        .clone()
}

/// Visitor that records every `GlobalId` referenced in expression /
/// pattern position, along with the call arity at the use site and
/// whether the use site requires the symbol to be a `[data]` constructor
/// (true when referenced from `Construct` in either an expression or a
/// pattern).
#[derive(Default)]
struct ExternRefCollector {
    calls: Vec<Ref>,
    /// Names synthesised by the printer for string / char / float
    /// literals — `string_lit__<sanitized>`, `char_lit__<sanitized>`,
    /// `float_lit__<sanitized>`. These need a `const <name>: bitstring.`
    /// declaration in the auto-decl block.
    lit_consts: Vec<String>,
}

struct Ref {
    id: GlobalId,
    arity: usize,
    is_constructor: bool,
}

impl ExternRefCollector {
    fn push(&mut self, id: GlobalId, arity: usize, is_constructor: bool) {
        self.calls.push(Ref {
            id,
            arity,
            is_constructor,
        });
    }
}

impl AstVisitor for ExternRefCollector {
    fn enter_expr_kind(&mut self, kind: &ExprKind) {
        match kind {
            ExprKind::App { head, args, .. } => {
                if let ExprKind::GlobalId(g) = &*head.kind {
                    self.push(*g, args.len(), false);
                }
            }
            ExprKind::GlobalId(g) => {
                self.push(*g, 0, false);
            }
            ExprKind::Construct {
                constructor,
                fields,
                ..
            } => {
                self.push(*constructor, fields.len(), true);
            }
            ExprKind::Literal(Literal::String(symbol)) => {
                self.lit_consts.push(format!(
                    "string_lit__{}",
                    sanitize_string_literal(symbol.as_ref())
                ));
            }
            ExprKind::Literal(Literal::Char(c)) => {
                self.lit_consts.push(format!(
                    "char_lit__{}",
                    sanitize_string_literal(&c.to_string())
                ));
            }
            ExprKind::Literal(Literal::Float {
                value, negative, ..
            }) => {
                let sign = if *negative { "neg_" } else { "" };
                self.lit_consts.push(format!(
                    "float_lit__{sign}{}",
                    sanitize_string_literal(value.as_ref())
                ));
            }
            _ => {}
        }
    }
    fn enter_pat_kind(&mut self, kind: &PatKind) {
        if let PatKind::Construct {
            constructor,
            fields,
            ..
        } = kind
        {
            self.push(*constructor, fields.len(), true);
        }
    }
}

/// Base64 alphabet for source-map VLQ encoding (RFC-style, `+/` tail).
const VLQ_B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Append the base64 VLQ encoding of a signed integer to `out` (source-map v3
/// "mappings" use this for every delta-encoded field).
fn vlq_encode(value: i64, out: &mut String) {
    // Sign goes in the low bit; the rest is the magnitude.
    let mut v: u64 = if value < 0 {
        ((value.unsigned_abs()) << 1) | 1
    } else {
        (value as u64) << 1
    };
    loop {
        let mut digit = (v & 0b1_1111) as usize;
        v >>= 5;
        if v != 0 {
            digit |= 0b10_0000; // continuation bit
        }
        out.push(VLQ_B64[digit] as char);
        if v == 0 {
            break;
        }
    }
}

/// Build a source-map v3 from harvested `(gen_line, gen_col, span)` anchors.
///
/// `header_lines` is the number of lines prepended (the `HEADER` preamble) ahead
/// of the rendered body, so generated line numbers line up with the final file.
/// Only anchors whose span resolves to a real on-disk file contribute a mapping
/// (phase-synthesized `Span::dummy()` nodes are skipped). Returns `None` when no
/// anchor maps anywhere.
fn build_source_map(
    out_file: &str,
    header_lines: usize,
    positions: &[(usize, usize, Span)],
) -> Option<SourceMap> {
    // Resolve each anchor to (gen_line, gen_col, source_index, src_line0, src_col0).
    let mut sources: Vec<String> = Vec::new();
    let source_index = |path: String, sources: &mut Vec<String>| -> usize {
        if let Some(i) = sources.iter().position(|p| *p == path) {
            i
        } else {
            sources.push(path);
            sources.len() - 1
        }
    };
    // (gen_line, gen_col, src_idx, src_line0, src_col0)
    let mut segs: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
    for (gl, gc, span) in positions {
        let Some(fs) = span.as_frontend_spans().first() else {
            continue;
        };
        let Some(path) = fs.filename.to_path() else {
            continue;
        };
        let idx = source_index(path.display().to_string(), &mut sources);
        // rustc lines are 1-based; source-map lines/cols are 0-based.
        let src_line0 = fs.lo.line.saturating_sub(1);
        segs.push((gl + header_lines, *gc, idx, src_line0, fs.lo.col));
    }
    if segs.is_empty() {
        return None;
    }
    // Order by generated position; encode line-by-line with delta fields.
    segs.sort_by_key(|s| (s.0, s.1));
    let max_line = segs.iter().map(|s| s.0).max().unwrap_or(0);
    let mut mappings = String::new();
    let (mut p_src, mut p_sl, mut p_sc) = (0i64, 0i64, 0i64);
    let mut seg_i = 0;
    for line in 0..=max_line {
        if line > 0 {
            mappings.push(';');
        }
        let mut p_gc = 0i64; // generated column resets each line
        let mut first = true;
        while seg_i < segs.len() && segs[seg_i].0 == line {
            let (_, gc, idx, sl, sc) = segs[seg_i];
            if !first {
                mappings.push(',');
            }
            first = false;
            vlq_encode(gc as i64 - p_gc, &mut mappings);
            vlq_encode(idx as i64 - p_src, &mut mappings);
            vlq_encode(sl as i64 - p_sl, &mut mappings);
            vlq_encode(sc as i64 - p_sc, &mut mappings);
            p_gc = gc as i64;
            p_src = idx as i64;
            p_sl = sl as i64;
            p_sc = sc as i64;
            seg_i += 1;
        }
    }
    Some(SourceMap {
        version: 3,
        file: out_file.to_string(),
        sourceRoot: String::new(),
        sources,
        // `cargo-hax` fills `sourcesContent` from disk when it writes the
        // `<file>.map` sidecar, so leave it empty here.
        sourcesContent: Vec::new(),
        names: Vec::new(),
        mappings,
    })
}
