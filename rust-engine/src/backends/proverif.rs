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

use std::collections::HashSet;
use std::sync::OnceLock;

use super::prelude::*;
use crate::ast::span::Span;
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
pub struct ProVerifPrinter {}

/// Preamble baked into every `lib.pvl` file.
///
/// Stage 2.0 collapses every Rust type to ProVerif `bitstring`. Booleans
/// become `True()`/`False()` data constructors and integer literals are
/// wrapped in `nat_lit(N)` so they land in the same universe.
const HEADER: &str = "\
(*****************************************)
(* Preamble                              *)
(*****************************************)

channel c.

fun construct_fail() : bitstring
reduc construct_fail() = fail.

const empty: bitstring.
letfun bitstring_default() = empty.
letfun bitstring_err() = let x = construct_fail() in bitstring_default().

fun Some(bitstring): bitstring [data].
fun None(): bitstring [data].
letfun Option_err() = let x = construct_fail() in None().

fun True(): bitstring [data].
fun False(): bitstring [data].
letfun bool_default() = False().
letfun bool_err() = let x = construct_fail() in False().

fun nat_lit(nat): bitstring.

fun logical_and(bitstring, bitstring): bitstring.
fun logical_or(bitstring, bitstring): bitstring.

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
}

impl Printer for ProVerifPrinter {}

impl ProVerifPrinter {
    /// Returns the joined identifier used by ProVerif declarations. Mirrors
    /// `print#concrete_ident` in the legacy printer.
    fn render_id(&self, id: &GlobalId) -> String {
        self.render_string(&id.view())
    }

    /// Names the bitstring conversion helpers for a ProVerif type rendering.
    /// Mirrors `print#field_accessor_prefix` in the legacy printer.
    fn accessor_name(&self, base: &str, field: &GlobalId) -> String {
        format!("accessor_{base}__{}", self.render_id(field))
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

            let fun_args_full = self.typed_args::<A>(&typed_args_vec);
            let fun_args_names = comma_sep!(typed_args_vec
                .iter()
                .map(|(id, _)| docs![self.render_id(id)]));

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
                        docs![hardline!(), accessor_call, " = ", self.render_id(id)]
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
                Literal::String(symbol) => format!("\"{symbol}\""),
                Literal::Char(c) => format!("'{c}'"),
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
                    format!("{}{value}", if *negative { "-" } else { "" })
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
            // Stage 2.0 uniform-bitstring: every type renders as `bitstring`
            // except a `Param(_)` (which should have been monomorphized away
            // before printing, but we keep a sensible fallback).
            match ty.kind() {
                TyKind::Param(local_id) => docs![local_id],
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
                    emit_error!("ProVerif backend does not support or-patterns")
                }
                PatKind::Array { .. } => {
                    emit_error!("ProVerif backend does not support array patterns")
                }
                PatKind::Deref { .. } => unreachable_by_invariant!(Drop_references),
                PatKind::Resugared(_) => {
                    emit_error!("ProVerif backend does not support resugared patterns")
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
                ExprKind::Array(_) => emit_error!("Array expressions not supported in ProVerif"),
                ExprKind::Borrow { .. } => unreachable_by_invariant!(Drop_references),
                ExprKind::AddressOf { .. } => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                ExprKind::Assign { .. } => unreachable_by_invariant!(Local_mutation),
                ExprKind::Loop { .. } => emit_error!("Loops not supported in ProVerif"),
                ExprKind::Break { .. } | ExprKind::Continue { .. } | ExprKind::Return { .. } => {
                    emit_error!("Early-exit control flow not supported in ProVerif")
                }
                ExprKind::Closure { .. } => emit_error!("Closures not supported in ProVerif"),
                ExprKind::Block { .. } => unreachable_by_invariant!(Drop_blocks),
                ExprKind::Quote { contents } => docs![contents],
                ExprKind::Resugared(_) => emit_error!("Unsupported resugared expression"),
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
                ItemKind::Impl { .. } => nil!(),
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

        fn impl_item(&self, _impl_item: &ImplItem) -> DocBuilder<A> {
            nil!()
        }

        fn error_node(&self, _error_node: &ErrorNode) -> DocBuilder<A> {
            docs!["(* error node *)"]
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

    /// The phase pipeline mirrors the OCaml `TransformToInputLanguage`
    /// at `engine/backends/proverif/proverif_backend.ml:887-910`.
    fn phases(&self) -> Vec<PhaseKind> {
        use crate::phase::{PhaseKind::*, legacy::LegacyOCamlPhase::*};
        vec![
            RejectUnsafe.into(),
            RejectRawOrMutPointer.into(),
            TransformHaxLibInline.into(),
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
        // Stage 2 adds protocol-aware resugarings (events, queries, processes).
        vec![]
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
        let contents = modules
            .into_iter()
            .map(|module: Module| printer.print(module).0)
            .collect::<Vec<String>>()
            .join("\n");
        vec![File {
            path,
            contents: format!("{}{}", HEADER, contents),
            sourcemap: None,
        }]
    }
}
