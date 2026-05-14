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
use camino::Utf8PathBuf;
use hax_lib_macros_types::AttrPayload;
use hax_types::engine_api::File;

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
    pub use crate::names::rust_primitives::hax::{cast_op, logical_op_and, logical_op_or};
    pub use crate::names::rust_primitives::hax::never_to_any;
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
const PRIMITIVES_PVL: &str =
    include_str!("../../../hax-lib/proof-libs/proverif/primitives.pvl");

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
*)

";

const INDENT: isize = 2;

impl RenderView for ProVerifPrinter {
    fn reserved_keywords() -> &'static HashSet<String> {
        static SET: OnceLock<HashSet<String>> = OnceLock::new();
        SET.get_or_init(|| {
            // Mirrors `ProVerifNamePolicy.reserved_words` in
            // `engine/backends/proverif/proverif_backend.ml:102-104`.
            [
                "among", "axiom", "channel", "choice", "clauses", "const", "def", "diff", "do",
                "elimtrue", "else", "equation", "equivalence", "event", "expand", "fail", "for",
                "forall", "foreach", "free", "fun", "get", "if", "implementation", "in",
                "inj-event", "insert", "lemma", "let", "letfun", "letproba", "new", "noninterf",
                "noselect", "not", "nounif", "or", "otherwise", "out", "param", "phase", "pred",
                "proba", "process", "proof", "public vars", "putbegin", "query", "reduc",
                "restriction", "secret", "select", "set", "suchthat", "sync", "table", "then",
                "type", "weaksecret", "yield",
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

impl Printer for ProVerifPrinter {}

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

    impl ProVerifPrinter {
        /// Print a list of typed parameters as `name: ty, ...`. Mirrors the
        /// `fun_args_full` helper in the legacy printer (`item_unwrapped`).
        fn typed_args<A: 'static + Clone>(
            &self,
            args: &[(GlobalId, Ty)],
        ) -> DocBuilder<A> {
            comma_sep!(args.iter().map(|(id, ty)| {
                docs![self.render_id(id), ": ", ty]
            }))
        }

        /// Emit a syntactically valid placeholder in expression position
        /// alongside a diagnostic. ProVerif comments (`(* ... *)`) aren't
        /// terms, so we surface `bitstring_err()` (declared in the preamble)
        /// instead — that keeps the surrounding letfun parseable.
        fn expr_error_placeholder<A: 'static + Clone>(
            &self,
            message: &str,
        ) -> DocBuilder<A> {
            <Self as PrettyAst<A>>::emit_diagnostic(
                self,
                hax_types::diagnostics::Kind::Unimplemented {
                    issue_id: None,
                    details: Some(message.into()),
                },
            );
            docs!["bitstring_err()", " (* ", message.to_string(), " *)"]
        }

        /// Print one match-arm as an `if-let` chain piece. Mirrors
        /// `match_arm` (`proverif_backend.ml:229-247`).
        fn match_arm<A: 'static + Clone>(
            &self,
            scrutinee: &Expr,
            arm: &Arm,
        ) -> DocBuilder<A> {
            match &*arm.pat.kind {
                PatKind::Wild => docs![&arm.body],
                PatKind::Construct { constructor, .. } if *constructor == names::ResultErr => {
                    docs!["bitstring_err()"]
                }
                _ => {
                    let pat: DocBuilder<A> = match &*arm.pat.kind {
                        PatKind::Constant { lit } => docs!["=", lit].parens(),
                        _ => docs![&arm.pat],
                    };
                    docs![
                        "let ",
                        pat,
                        " = ",
                        docs![scrutinee],
                        " in ",
                        docs![&arm.body]
                    ]
                }
            }
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
            let arg_types_doc =
                comma_sep!(typed_args_vec.iter().map(|(_, ty)| docs![ty]));

            let fun_line = docs![
                "fun ",
                constructor_name.clone(),
                arg_types_doc.parens(),
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
            // inside the rule. Append a `_v` suffix on each forall-bound
            // variable to keep them fresh.
            let bind_name = |id: &GlobalId| format!("{}_v", self.render_id(id));
            let fun_args_full: DocBuilder<A> = comma_sep!(typed_args_vec.iter().map(|(id, ty)| {
                docs![bind_name(id), ": ", ty]
            }));
            let fun_args_names: DocBuilder<A> = comma_sep!(typed_args_vec
                .iter()
                .map(|(id, _)| docs![bind_name(id)]));

            let reduc_pieces: Vec<DocBuilder<A>> = typed_args_vec
                .iter()
                .map(|(id, _ty)| {
                    let accessor = self.accessor_name(&base, id);
                    let constructor_call = docs![
                        constructor_name.clone(),
                        docs![fun_args_names.clone()].parens()
                    ];
                    let accessor_call =
                        docs![accessor, docs![constructor_call].parens()];
                    docs![
                        "reduc forall ",
                        docs![fun_args_full.clone()],
                        ";",
                        docs![hardline!(), accessor_call, " = ", bind_name(id)]
                            .nest(INDENT)
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
                let rest = rest.replace(' ', "_").replace('+', "_");
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
                Literal::Int { value, negative, .. } => {
                    // ProVerif's `nat` is unsigned; spell negative literals as
                    // `nat_lit(0 - N)` (the only way to coax a negative term
                    // into the universal bitstring encoding).
                    if *negative {
                        format!("nat_lit(0 - {value})")
                    } else {
                        format!("nat_lit({value})")
                    }
                }
                Literal::Float { value, negative, .. } => {
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
            docs![Self::escape(&symbol.to_string())]
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
                    is_struct,
                } => {
                    let args = if fields.is_empty() {
                        nil!()
                    } else if *is_struct && fields.iter().all(|(_, p)| {
                        matches!(*p.kind, PatKind::Wild)
                    }) {
                        // record-style placeholder
                        nil!()
                    } else {
                        comma_sep!(fields.iter().map(|(_, p)| {
                            // tuple-elem patterns are emitted with their type
                            // ascription if they're bare bindings (matches
                            // `tuple_elem_pat'`).
                            match &*p.kind {
                                PatKind::Binding {
                                    sub_pat: None, var, mutable: false,
                                    mode: BindingMode::ByValue,
                                } => docs![var, ": ", &p.ty],
                                _ => docs![p],
                            }
                        }))
                    };
                    if fields.is_empty() {
                        docs![constructor, "()"]
                    } else {
                        docs![constructor, args.parens()]
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
                            details: Some(
                                "ProVerif backend does not support or-patterns".into(),
                            ),
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
                ExprKind::App {
                    head, args, ..
                } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::into) => {
                    // After Stage 2.0 the surface type of every value is
                    // `bitstring`, so `Into::into` is a no-op.
                    args.first().map(|a| docs![a]).unwrap_or(nil!())
                }
                ExprKind::App {
                    head, ..
                } if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::never_to_any) => {
                    docs!["bitstring_err()"]
                }

                // ===== Result-typed expressions (lines 712-730) =====
                ExprKind::Construct { constructor, fields, .. }
                    if *constructor == names::ResultOk =>
                {
                    if let Some((_, inner)) = fields.first() {
                        docs![inner]
                    } else {
                        docs![""]
                    }
                }
                ExprKind::Construct { constructor, .. }
                    if *constructor == names::ResultErr =>
                {
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
                ExprKind::App { head, args, .. }
                    if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::logical_op_and) =>
                {
                    let lhs = args.first().map(|a| docs![a]).unwrap_or(nil!());
                    let rhs = args.get(1).map(|a| docs![a]).unwrap_or(nil!());
                    docs!["logical_and", comma_sep!(vec![lhs, rhs]).parens()]
                }
                ExprKind::App { head, args, .. }
                    if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::logical_op_or) =>
                {
                    let lhs = args.first().map(|a| docs![a]).unwrap_or(nil!());
                    let rhs = args.get(1).map(|a| docs![a]).unwrap_or(nil!());
                    docs!["logical_or", comma_sep!(vec![lhs, rhs]).parens()]
                }
                ExprKind::App { head, args, .. }
                    if matches!(&*head.kind, ExprKind::GlobalId(g) if *g == names::cast_op) =>
                {
                    // Cast → just the inner argument (line 401).
                    args.first().map(|a| docs![a]).unwrap_or(nil!())
                }

                // ===== Construct: Some / None / generic (lines 429-449) =====
                ExprKind::Construct { constructor, .. } if *constructor == names::OptionNone => {
                    docs!["None()"]
                }
                ExprKind::Construct { constructor, fields, .. }
                    if *constructor == names::OptionSome =>
                {
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
                        docs![constructor, payload.parens()]
                    } else {
                        let payload = comma_sep!(fields.iter().map(|(_, v)| docs![v]));
                        docs![constructor, payload.parens()]
                    }
                }

                // ===== Match → if-let chain (lines 450-456) =====
                ExprKind::Match { scrutinee, arms } => {
                    let pieces: Vec<DocBuilder<A>> = arms
                        .iter()
                        .map(|arm| self.match_arm(scrutinee, arm))
                        .collect();
                    intersperse!(pieces, docs![hardline!(), "else "])
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
                        " in ",
                        docs![then].parens(),
                        " else ",
                        docs![e].parens()
                    ],
                    None => docs![
                        "let (=True()) = ",
                        condition,
                        " in ",
                        docs![then].parens()
                    ],
                },
                ExprKind::Let { lhs, rhs, body } => docs![
                    "let ",
                    lhs,
                    " = ",
                    docs![rhs].parens(),
                    " in",
                    hardline!(),
                    body
                ],

                // ===== expr_app fallback (357-372) =====
                ExprKind::App {
                    head, args, ..
                } => {
                    let head_doc = docs![head];
                    if args.is_empty() {
                        docs![head_doc, "()"]
                    } else {
                        docs![head_doc, comma_sep!(args.iter().map(|a| docs![a])).parens()]
                    }
                }

                ExprKind::Literal(literal) => docs![literal],
                ExprKind::GlobalId(g) => docs![g],
                ExprKind::LocalId(local_id) => docs![local_id],
                ExprKind::Ascription { e, ty: _ } => docs![e],
                ExprKind::Array(_) => self.expr_error_placeholder::<A>(
                    "Array expressions not supported in ProVerif",
                ),
                ExprKind::Borrow { .. } => unreachable_by_invariant!(Drop_references),
                ExprKind::AddressOf { .. } => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                ExprKind::Assign { .. } => unreachable_by_invariant!(Local_mutation),
                ExprKind::Loop { .. } => self.expr_error_placeholder::<A>(
                    "Loops not supported in ProVerif",
                ),
                ExprKind::Break { .. } | ExprKind::Continue { .. } | ExprKind::Return { .. } => {
                    self.expr_error_placeholder::<A>(
                        "Early-exit control flow not supported in ProVerif",
                    )
                }
                ExprKind::Closure { .. } => self.expr_error_placeholder::<A>(
                    "Closures not supported in ProVerif",
                ),
                ExprKind::Block { .. } => unreachable_by_invariant!(Drop_blocks),
                ExprKind::Quote { contents } => docs![contents],
                ExprKind::Resugared(_) => self.expr_error_placeholder::<A>(
                    "Unsupported resugared expression",
                ),
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
            docs![&variant.name, args.parens()]
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

            match item.kind() {
                ItemKind::Fn {
                    name, body, params, ..
                } => {
                    if params.is_empty() {
                        // Empty-param `fn`s are Rust consts. After Stage 2.0
                        // every value lives in `bitstring`.
                        docs!["const ", name, ": bitstring."]
                    } else if as_constructor {
                        // `#[hax::proverif::constructor]` (lines 543-559).
                        let arg_types =
                            comma_sep!(params.iter().map(|p| docs![&p.ty]));
                        docs![
                            "(* marked as constructor *)",
                            hardline!(),
                            "fun ",
                            name,
                            arg_types.parens(),
                            ": bitstring [data]."
                        ]
                    } else {
                        // Regular letfun (lines 560-588).
                        let comment = if as_handwritten {
                            docs!["(* REPLACE by handwritten model *)", hardline!()]
                        } else {
                            nil!()
                        };
                        let params_doc =
                            comma_sep!(params.iter().map(|p| docs![p]));
                        let body_doc: DocBuilder<A> = if as_handwritten {
                            docs!["bitstring_default()"]
                        } else {
                            docs![body]
                        };
                        docs![
                            comment,
                            "letfun ",
                            name,
                            params_doc.parens(),
                            " =",
                            hardline!(),
                            docs![body_doc].nest(INDENT),
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
            }
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
            match &impl_item.kind {
                // Associated types are bitstring; nothing to declare.
                ImplItemKind::Type { .. } => nil!(),
                ImplItemKind::Fn { body, params } => {
                    if params.is_empty() {
                        docs!["const ", name, ": bitstring."]
                    } else {
                        let params_doc =
                            comma_sep!(params.iter().map(|p| docs![p]));
                        docs![
                            "letfun ",
                            name,
                            params_doc.parens(),
                            " =",
                            hardline!(),
                            docs![body].nest(INDENT),
                            "."
                        ]
                    }
                }
                ImplItemKind::Resugared(ResugaredImplItemKind::Constant {
                    body: _,
                }) => {
                    // Associated constants land as opaque `bitstring`. Users
                    // who care about the value can override with a verbatim
                    // `proverif_replace!` body.
                    docs!["const ", name, ": bitstring."]
                }
                ImplItemKind::Error(err) => docs![err],
            }
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
            SimplifyMatchReturn.into(),
            LocalMutation.into(),
            RejectContinue.into(),
            RejectDyn.into(),
            ReorderFields.into(),
            BundleCycles.into(),
            SortItemsNamespaceWise.into(),
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

    fn modules_to_files(&self, modules: Vec<Module>, mut printer: Self::Printer) -> Vec<File> {
        if modules.is_empty() {
            return vec![];
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
        // Render the body.
        let contents = modules
            .into_iter()
            .map(|module: Module| printer.print(module).0)
            .collect::<Vec<String>>()
            .join("\n");
        // Scan the rendered body for the names it already declares
        // (including ones synthesized by `proverif_replace_body!`
        // quote injections such as `reduc forall ...; foo(...) = ...`),
        // then emit an auto-decl block only for what's still missing.
        let externals = self.format_external_decls(&referenced, &contents);
        vec![File {
            path,
            contents: format!("{HEADER}{externals}\n{contents}"),
            sourcemap: None,
        }]
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
                let args = std::iter::repeat("bitstring")
                    .take(info.arity)
                    .collect::<Vec<_>>()
                    .join(", ");
                // Every auto-declared function is marked `[data]`. Without
                // it, ProVerif treats `f(a,b)` and `f(c,d)` as
                // indistinguishable opaque outputs, which collapses
                // arguments in symbolic reasoning. `[data]` makes the
                // symbol injective so the analyzer can still tell the
                // inputs apart — exactly what we want for primitives we
                // know nothing else about. (`[data]` is also required for
                // any name used in `let pat(..) = ...` / `Construct(..)`
                // position.)
                decls.push(format!("fun {name}({args}): bitstring [data]."));
            }
        }
        if decls.is_empty() {
            String::new()
        } else {
            format!(
                "(*****************************************)\n\
                 (* Auto-declared external symbols        *)\n\
                 (*****************************************)\n\
                 {}\n",
                decls.join("\n")
            )
        }
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
    ///      reduc forall
    ///        b1: t1,
    ///        b2: t2;
    ///
    ///        F(args)
    ///        = ...
    /// We need to pick up `F` in all three shapes.
    enum ReducState {
        None,
        SeenReduc,     // saw bare `reduc`, waiting for `forall`
        SeenHeader,    // saw `reduc forall`, waiting for `;`
        AwaitingHead,  // saw `;`, looking for the next non-empty token
    }
    let mut out: Vec<String> = Vec::new();
    let mut state = ReducState::None;
    for line in rendered.lines() {
        let s = line.trim_start();
        // `fun NAME(...)`, `letfun NAME(...)`, `const NAME: ...`
        for kw in ["fun ", "letfun ", "const "] {
            if let Some(rest) = s.strip_prefix(kw) {
                let end = rest
                    .find(|c: char| c == '(' || c == ':' || c == ' ' || c == '\t')
                    .unwrap_or(rest.len());
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
                let end = head
                    .find(|c: char| c == '(' || c == ':' || c == ' ')
                    .unwrap_or(head.len());
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
