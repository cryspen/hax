//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use std::collections::HashSet;
use std::sync::LazyLock;

use super::prelude::*;
use crate::{
    ast::identifiers::global_id::view::{ConstructorKind, PathSegment, TypeDefKind},
    phase::{
        explicit_monadic::ExplicitMonadic, reject_not_do_lean_dsl::RejectNotDoLeanDSL,
        unreachable_by_invariant,
    },
};

mod binops {
    pub use crate::names::core::ops::index::*;
    pub use crate::names::rust_primitives::hax::machine_int::*;
    pub use crate::names::rust_primitives::hax::{logical_op_and, logical_op_or};
}

use crate::names::rust_primitives::hax::explicit_monadic::{lift, pure};
const LIFT: GlobalId = lift;
const PURE: GlobalId = pure;

/// The Lean printer
#[setup_span_handling_struct]
#[derive(Default, Clone)]
pub struct LeanPrinter;

const INDENT: isize = 2;

static RESERVED_KEYWORDS: LazyLock<HashSet<String>> = LazyLock::new(|| {
    HashSet::from_iter(
        [
            "end",
            "def",
            "abbrev",
            "theorem",
            "example",
            "inductive",
            "structure",
            "from",
        ]
        .iter()
        .map(|s| s.to_string()),
    )
});

impl RenderView for LeanPrinter {
    fn separator(&self) -> &str {
        "."
    }
    fn render_path_segment(&self, chunk: &PathSegment) -> Vec<String> {
        fn uppercase_first(s: &str) -> String {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
            }
        }
        // Returning None indicates that the default rendering should be used
        (match chunk.kind() {
            AnyKind::Mod => {
                let mut chunks = default::render_path_segment(self, chunk);
                for c in &mut chunks {
                    *c = uppercase_first(c);
                }
                Some(chunks)
            }
            AnyKind::Constructor(ConstructorKind::Constructor { ty })
                if matches!(ty.kind(), TypeDefKind::Struct) =>
            {
                Some(vec![
                    self.render_path_segment_payload(chunk.payload())
                        .to_string(),
                    "mk".to_string(),
                ])
            }
            AnyKind::Field { named: _, parent } => match parent.kind() {
                ConstructorKind::Constructor { ty }
                    if matches!(&ty.kind(), TypeDefKind::Struct) =>
                {
                    chunk.parent().map(|parent| {
                        vec![
                            self.escape(
                                self.render_path_segment_payload(parent.payload())
                                    .to_string(),
                            ),
                            self.escape(
                                self.render_path_segment_payload(chunk.payload())
                                    .to_string(),
                            ),
                        ]
                    })
                }
                _ => None,
            },
            _ => None,
        })
        .unwrap_or(default::render_path_segment(self, chunk))
    }
}

impl Printer for LeanPrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![
            Box::new(BinOp::new(&[
                binops::add,
                binops::sub,
                binops::mul,
                binops::rem,
                binops::div,
                binops::shr,
                binops::bitand,
                binops::bitxor,
                binops::logical_op_and,
                binops::logical_op_or,
                binops::Index::index,
            ])),
            Box::new(FunctionsToConstants),
            Box::new(LetPure),
        ]
    }
}

/// The Lean backend
pub struct LeanBackend;

impl Backend for LeanBackend {
    type Printer = LeanPrinter;

    fn module_path(&self, module: &Module) -> camino::Utf8PathBuf {
        camino::Utf8PathBuf::from_iter(self.printer().render_strings(&module.ident.view()))
            .with_extension("lean")
    }

    fn phases(&self) -> Vec<Box<dyn crate::phase::Phase>> {
        vec![Box::new(RejectNotDoLeanDSL), Box::new(ExplicitMonadic)]
    }
}

impl LeanPrinter {
    /// A filter for items blacklisted by the Lean backend : returns false if
    /// the item is definitely not printable, but might return true on
    /// unsupported items
    pub fn printable_item(item: &Item) -> bool {
        match &item.kind {
            // Anonymous consts
            ItemKind::Resugared(ResugaredItemKind::Constant {
                name,
                body: _,
                generics: _,
            }) if name.is_anonymous_const() => false,
            // Other unprintable items
            ItemKind::Error(_) | ItemKind::NotImplementedYet | ItemKind::Use { .. } => false,
            // Printable items
            ItemKind::Fn { .. }
            | ItemKind::TyAlias { .. }
            | ItemKind::Type { .. }
            | ItemKind::Trait { .. }
            | ItemKind::Impl { .. }
            | ItemKind::Alias { .. }
            | ItemKind::Resugared(_)
            | ItemKind::Quote { .. } => true,
        }
    }

    /// Render a global id using the Rendering strategy of the Lean printer. Works for both concrete
    /// and projector ids. TODO: https://github.com/cryspen/hax/issues/1660
    pub fn render_id(&self, id: &GlobalId) -> String {
        self.render_string(&id.view())
    }

    /// Escapes local identifiers (prefixing reserved keywords with an underscore).
    /// TODO: This should be treated directly in the name rendering engine, see
    /// https://github.com/cryspen/hax/issues/1630
    pub fn escape(&self, id: String) -> String {
        let id = id.replace([' ', '<', '>'], "_");
        if id.is_empty() {
            "_ERROR_EMPTY_ID_".to_string()
        } else if RESERVED_KEYWORDS.contains(&id) || id.starts_with(|c: char| c.is_ascii_digit()) {
            format!("_{id}")
        } else {
            id
        }
    }

    /// Renders the last, most local part of an id. Used for named arguments of constructors.
    pub fn render_last(&self, id: &GlobalId) -> String {
        let id = self
            .render(&id.view())
            .path
            .last()
            // TODO: Should be ensured by the rendering engine; see
            // https://github.com/cryspen/hax/issues/1660
            .expect("Segments should always be non-empty")
            .clone();
        self.escape(id)
    }
}

/// Render parameters, adding a line after each parameter
impl<A: 'static + Clone> ToDocument<LeanPrinter, A> for Vec<Param> {
    fn to_document(&self, printer: &LeanPrinter) -> DocBuilder<A> {
        printer.params(self)
    }
}

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
const _: () = {
    // Emits a CLI error with a github issue number, and prints "sorry" in the lean output
    macro_rules! emit_error {($($tt:tt)*) => {disambiguated_todo!($($tt)*)};}

    // Insert a new line in a doc (pretty)
    macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}

    // Concatenate docs (pretty )
    macro_rules! concat {($($tt:tt)*) => {disambiguated_concat!($($tt)*)};}

    // Given an iterable `[A,B, ... , C]` and a separator `S`, create the doc `ASBS...CS`
    macro_rules! zip_right {
        ($a:expr, $sep:expr) => {
            docs![concat!($a.into_iter().map(|a| docs![a, $sep]))]
        };
    }

    // Given an iterable `[A,B, ... , C]` and a separator `S`, create the doc `SASB...SC`
    macro_rules! zip_left {
        ($sep:expr, $a:expr) => {
            docs![concat!($a.into_iter().map(|a| docs![$sep, a]))]
        };
    }

    // Prints a one-line comment
    macro_rules! comment {
        ($e:expr) => {
            docs!["-- ", $e]
        };
    }

    // Methods for handling arguments of variants (or struct constructor)
    impl LeanPrinter {
        /// Prints arguments a variant or constructor of struct, using named or unamed arguments based
        /// on the `is_record` flag. Used for both expressions and patterns
        pub fn arguments<A: 'static + Clone, D>(
            &self,
            fields: &[(GlobalId, D)],
            is_record: &bool,
        ) -> DocBuilder<A>
        where
            D: ToDocument<Self, A>,
        {
            if *is_record {
                self.named_arguments(fields)
            } else {
                self.positional_arguments(fields)
            }
        }

        /// Prints fields of structures (when in braced notation)
        fn struct_fields<A: 'static + Clone, D>(&self, fields: &[(GlobalId, D)]) -> DocBuilder<A>
        where
            D: ToDocument<Self, A>,
        {
            docs![intersperse!(
                fields
                    .iter()
                    .map(|(id, e)| { docs![self.render_last(id), reflow!(" := "), e].group() }),
                docs![",", line!()]
            )]
            .group()
        }
        /// Prints named arguments (record) of a variant or constructor of struct
        fn named_arguments<A: 'static + Clone, D>(&self, fields: &[(GlobalId, D)]) -> DocBuilder<A>
        where
            D: ToDocument<Self, A>,
        {
            docs![intersperse!(
                fields.iter().map(|(id, e)| {
                    docs![self.render_last(id), reflow!(" := "), e]
                        .parens()
                        .group()
                }),
                line!()
            )]
            .group()
        }

        /// Prints positional arguments (tuple) of a variant or constructor of struct
        fn positional_arguments<A: 'static + Clone, D>(
            &self,
            fields: &[(GlobalId, D)],
        ) -> DocBuilder<A>
        where
            D: ToDocument<Self, A>,
        {
            docs![intersperse!(fields.iter().map(|(_, e)| e), line!())].group()
        }

        /// Prints parameters of functions (items, trait items, impl items)
        fn params<A: 'static + Clone>(&self, params: &Vec<Param>) -> DocBuilder<A> {
            zip_right!(params, line!())
        }

        /// Renders expressions with an explicit ascription `(e : Result ty)`. Used for the body of closure, for
        /// numeric literals, etc.
        fn expr_typed_result<A: 'static + Clone>(&self, expr: &Expr) -> DocBuilder<A> {
            docs![
                expr,
                reflow!(" : "),
                docs!["Result", line!(), &expr.ty].group()
            ]
            .group()
        }

        fn pat_typed<A: 'static + Clone>(&self, pat: &Pat) -> DocBuilder<A> {
            docs![pat, reflow!(" :"), line!(), &pat.ty].parens().group()
        }

        fn do_block<A: 'static + Clone, D: ToDocument<Self, A>>(&self, body: D) -> DocBuilder<A> {
            docs!["do", line!(), body].group()
        }
    }

    impl<A: 'static + Clone> PrettyAst<A> for LeanPrinter {
        const NAME: &'static str = "Lean";

        /// Produce a non-panicking placeholder document. In general, prefer the use of the helper macro [`todo_document!`].
        fn todo_document(&self, message: &str, issue_id: Option<u32>) -> DocBuilder<A> {
            <Self as PrettyAst<A>>::emit_diagnostic(
                self,
                hax_types::diagnostics::Kind::Unimplemented {
                    issue_id,
                    details: Some(message.into()),
                },
            );
            text!("sorry")
        }

        fn module(&self, module: &Module) -> DocBuilder<A> {
            let items = &module.items;
            docs![
                intersperse!(
                    "
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


"
                    .lines(),
                    hardline!(),
                ),
                intersperse!(
                    items
                        .iter()
                        .filter(|item| LeanPrinter::printable_item(item)),
                    docs![hardline!(), hardline!()]
                )
            ]
        }

        fn global_id(&self, global_id: &GlobalId) -> DocBuilder<A> {
            docs![self.render_id(global_id)]
        }

        /// Render generics, adding a space after each parameter
        fn generics(
            &self,
            Generics {
                params,
                constraints,
            }: &Generics,
        ) -> DocBuilder<A> {
            docs![
                zip_right!(params, line!()),
                zip_right!(
                    constraints
                        .iter()
                        .map(|constraint| docs![constraint].brackets()),
                    line!()
                ),
            ]
            .group()
        }

        fn generic_constraint(&self, generic_constraint: &GenericConstraint) -> DocBuilder<A> {
            match generic_constraint {
                GenericConstraint::Type(impl_ident) => docs![impl_ident],
                GenericConstraint::Projection(_) => {
                    emit_error!(issue 1710, "Unsupported equality constraints on associated types")
                }
                GenericConstraint::Lifetime(_) => unreachable_by_invariant!(Drop_references),
            }
        }

        fn generic_param(&self, generic_param: &GenericParam) -> DocBuilder<A> {
            match generic_param.kind() {
                GenericParamKind::Type => docs![&generic_param.ident, reflow!(" : Type")]
                    .parens()
                    .group(),
                GenericParamKind::Lifetime => unreachable_by_invariant!(Drop_references),
                GenericParamKind::Const { .. } => {
                    emit_error!(issue 1711, "Const parameters are not yet supported")
                }
            }
        }

        fn expr(&self, Expr { kind, ty, meta: _ }: &Expr) -> DocBuilder<A> {
            match &**kind {
                ExprKind::Literal(int_lit @ Literal::Int { .. }) => {
                    docs![int_lit, reflow!(" : "), ty].parens().group()
                }
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    if let Some(else_branch) = else_ {
                        docs![
                            docs!["if", line!(), condition, reflow!(" then")].group(),
                            docs![line!(), then].nest(INDENT),
                            line!(),
                            "else",
                            docs![line!(), else_branch].nest(INDENT)
                        ]
                        .group()
                    } else {
                        unreachable_by_invariant!(Local_mutation)
                    }
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls: _,
                    trait_: _,
                } => {
                    match (&args[..], &generic_args[..], head.kind()) {
                        ([arg], [], ExprKind::GlobalId(LIFT)) => docs![reflow!("← "), arg].parens(),
                        ([arg], [], ExprKind::GlobalId(PURE)) => {
                            docs![reflow!("pure "), arg].parens()
                        }
                        _ => {
                            // Fallback for any application
                            let generic_args = (!generic_args.is_empty()).then_some(
                                docs![line!(), intersperse!(generic_args, line!())].group(),
                            );
                            let args = (!args.is_empty())
                                .then_some(docs![line!(), intersperse!(args, line!())].group());
                            docs![head, generic_args, args]
                                .parens()
                                .nest(INDENT)
                                .group()
                        }
                    }
                }
                ExprKind::Literal(literal) => docs![literal],
                ExprKind::Array(exprs) => docs![
                    "#v[",
                    intersperse!(exprs, docs![",", line!()])
                        .nest(INDENT)
                        .group()
                        .align(),
                    "]"
                ]
                .group(),
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    if fields.is_empty() && base.is_none() {
                        docs![constructor]
                    } else if let Some(base) = base {
                        if !(*is_record && *is_struct) {
                            unreachable!(
                                "Constructors with base expressions are necessarily structs with record-like arguments"
                            )
                        }
                        docs![base, line!(), reflow!("with "), self.struct_fields(fields)]
                            .braces()
                            .group()
                    } else {
                        docs![constructor, line!(), self.arguments(fields, is_record)]
                            .nest(INDENT)
                            .parens()
                            .group()
                    }
                }
                ExprKind::Let { lhs, rhs, body }
                | ExprKind::Resugared(ResugaredExprKind::LetPure { lhs, rhs, body }) => {
                    let binder = if matches!(**kind, ExprKind::Let { .. }) {
                        " ←"
                    } else {
                        " :="
                    };
                    docs![
                        docs![
                            docs![
                                "let",
                                line!(),
                                // TODO: Improve treatment of patterns in general. see
                                // https://github.com/cryspen/hax/issues/1712
                                match *lhs.kind.clone() {
                                    PatKind::Binding {
                                        mutable: false,
                                        var,
                                        mode: BindingMode::ByValue,
                                        sub_pat: None,
                                    } => docs![&var, reflow!(" : "), &lhs.ty],
                                    _ => docs![lhs],
                                },
                            ]
                            .group(),
                            binder,
                            line!(),
                            rhs,
                            ";"
                        ]
                        .nest(INDENT)
                        .group(),
                        line!(),
                        body,
                    ]
                }
                ExprKind::GlobalId(global_id) => docs![global_id],
                ExprKind::LocalId(local_id) => docs![local_id],
                ExprKind::Ascription { e, ty } => docs![e, reflow!(" : "), ty].parens().group(),
                ExprKind::Closure {
                    params,
                    body,
                    captures: _,
                } => docs![
                    reflow!("fun "),
                    intersperse!(params, line!()).group(),
                    reflow!(" => "),
                    self.do_block(self.expr_typed_result(body)).parens()
                ]
                .parens()
                .group()
                .nest(INDENT),

                ExprKind::Resugared(ResugaredExprKind::BinOp { op, lhs, rhs, .. }) => {
                    // TODO : refactor this, moving this code directly in the `App` node (see
                    // https://github.com/cryspen/hax/issues/1705)
                    if *op == binops::Index::index {
                        return docs![lhs, "[", line_!(), rhs, line_!(), "]_?"]
                            .nest(INDENT)
                            .group();
                    }
                    let symbol = match *op {
                        binops::add => "+?",
                        binops::sub => "-?",
                        binops::mul => "*?",
                        binops::div => "/?",
                        binops::rem => "%?",
                        binops::shr => ">>>?",
                        binops::bitand => "&&&?",
                        binops::bitxor => "^^^?",
                        binops::logical_op_and => "&&?",
                        binops::logical_op_or => "||?",
                        _ => unreachable!(),
                    };
                    docs![lhs, line!(), docs![symbol, softline!(), rhs].group()]
                        .group()
                        .nest(INDENT)
                        .parens()
                }
                ExprKind::Resugared(ResugaredExprKind::Tuple { .. }) => {
                    unreachable!("This printer doesn't use the tuple resugaring")
                }
                ExprKind::Match { scrutinee, arms } => docs![
                    docs![
                        "match",
                        docs![line!(), scrutinee].nest(INDENT),
                        line!(),
                        "with"
                    ]
                    .group(),
                    docs![line!(), intersperse!(arms, line!())]
                        .group()
                        .nest(INDENT),
                ]
                .group(),

                ExprKind::Borrow { .. } | ExprKind::Deref(_) => {
                    unreachable_by_invariant!(Drop_references)
                }
                ExprKind::AddressOf { .. } => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                ExprKind::Assign { .. } => unreachable_by_invariant!(Local_mutation),
                ExprKind::Loop { .. } => unreachable_by_invariant!(Functionalize_loops),
                ExprKind::Break { .. } | ExprKind::Return { .. } | ExprKind::Continue { .. } => {
                    unreachable_by_invariant!(Drop_break_continue_return)
                }
                ExprKind::Block { .. } => unreachable_by_invariant!(Drop_blocks),
                ExprKind::Quote { contents } => docs![contents],
                ExprKind::Error(error_node) => docs![error_node],
            }
        }

        fn arm(&self, arm: &Arm) -> DocBuilder<A> {
            if let Some(_guard) = &arm.guard {
                unreachable_by_invariant!(Drop_match_guards)
            } else {
                docs![
                    reflow!("| "),
                    &arm.pat,
                    line!(),
                    docs!["=>", line!(), &arm.body].nest(INDENT).group()
                ]
                .nest(INDENT)
                .group()
            }
        }

        fn pat(&self, pat: &Pat) -> DocBuilder<A> {
            match &*pat.kind {
                PatKind::Wild => docs!["_"],
                PatKind::Ascription { pat, ty: _ } => docs![pat],
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => match (mutable, mode, sub_pat) {
                    (true, _, _) => unreachable_by_invariant!(Local_mutation),
                    (false, BindingMode::ByRef(_), _) => unreachable_by_invariant!(Drop_references),
                    (false, BindingMode::ByValue, None) => docs![var],
                    (false, BindingMode::ByValue, Some(_)) => {
                        emit_error!(issue 1712, "Unsupported as-pattern")
                    }
                },
                PatKind::Or { sub_pats } => docs![intersperse!(sub_pats, reflow!(" | "))].group(),
                PatKind::Array { .. } => {
                    emit_error!(issue 1712, "Unsupported pattern-matching on arrays")
                }
                PatKind::Deref { .. } => unreachable_by_invariant!(Drop_references),
                PatKind::Constant { .. } => {
                    emit_error!(issue 1712, "Unsupported pattern-matching on constants")
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    if *is_struct {
                        if !*is_record {
                            // Tuple-like structure, using positional arguments
                            docs![
                                "⟨",
                                intersperse!(
                                    fields.iter().map(|field| { docs![&field.1] }),
                                    docs![",", line!()]
                                )
                                .align()
                                .group(),
                                "⟩"
                            ]
                            .align()
                            .group()
                        } else {
                            // Structure-like structure, using named arguments
                            docs![intersperse!(
                                fields.iter().map(|(id, pat)| {
                                    docs![self.render_last(id), reflow!(" := "), pat].group()
                                }),
                                docs![",", line!()]
                            )]
                            .align()
                            .braces()
                            .group()
                        }
                    } else {
                        // Variant
                        docs![
                            constructor,
                            line!(),
                            self.arguments(fields, is_record).align()
                        ]
                        .parens()
                        .group()
                        .nest(INDENT)
                    }
                }
                PatKind::Resugared(_) => {
                    unreachable!("This backend does not use resugarings on patterns")
                }
                PatKind::Error(_) => {
                    // TODO : Should be made unreachable by https://github.com/cryspen/hax/pull/1672
                    text!("sorry")
                }
            }
        }

        fn ty(&self, ty: &Ty) -> DocBuilder<A> {
            match ty.kind() {
                TyKind::Primitive(primitive_ty) => docs![primitive_ty],
                TyKind::App { head, args } => {
                    if args.is_empty() {
                        docs![head]
                    } else {
                        docs![head, zip_left!(line!(), args)]
                            .parens()
                            .group()
                            .nest(INDENT)
                    }
                }
                TyKind::Arrow { inputs, output } => docs![
                    zip_right!(inputs, docs![line!(), reflow!("-> ")]),
                    "Result ",
                    output
                ]
                .group(),
                TyKind::Param(local_id) => docs![local_id],
                TyKind::Slice(ty) => docs!["RustSlice", line!(), ty].parens().group(),
                TyKind::Array { ty, length } => {
                    let v = length.kind().clone();
                    let ExprKind::Literal(int_lit @ Literal::Int { .. }) = v else {
                        emit_error!(issue 1713, "Unsupported arrays where the size is not an integer literal")
                    };
                    docs!["RustArray", line!(), ty, line!(), &int_lit]
                        .parens()
                        .group()
                }
                TyKind::AssociatedType { impl_, item } => {
                    let kind = impl_.kind();
                    match &kind {
                        ImplExprKind::Self_ => docs![self.render_last(item)],
                        _ => {
                            emit_error!(issue 1710, "Unsupported non trait-local associated types")
                        }
                    }
                }
                TyKind::Ref { .. } => unreachable_by_invariant!(Drop_references),
                TyKind::RawPointer => unreachable_by_invariant!(Reject_raw_or_mut_pointer),
                TyKind::Opaque(_) => emit_error!(issue 1714, "Unsupported opaque type definitions"),
                TyKind::Dyn(_) => emit_error!(issue 1708, "Unsupported `dyn` traits"),
                TyKind::Resugared(resugared_ty_kind) => match resugared_ty_kind {
                    ResugaredTyKind::Tuple(_) => {
                        unreachable!("This backend does not use tuple resugaring (yet)")
                    }
                },
                TyKind::Error(e) => docs![e],
            }
        }

        fn literal(&self, literal: &Literal) -> DocBuilder<A> {
            docs![match literal {
                Literal::String(symbol) => format!("\"{symbol}\""),
                Literal::Char(c) => format!("'{c}'"),
                Literal::Bool(b) => format!("{b}"),
                Literal::Int {
                    value,
                    negative,
                    kind: _,
                } => format!("{}{value}", if *negative { "-" } else { "" }),
                Literal::Float { .. } => emit_error!(issue 1715, "Unsupported Float literal"),
            }]
        }

        fn local_id(&self, local_id: &LocalId) -> DocBuilder<A> {
            // TODO: should be done by name rendering, see https://github.com/cryspen/hax/issues/1630
            docs![self.escape(local_id.0.to_string())]
        }

        fn spanned_ty(&self, spanned_ty: &SpannedTy) -> DocBuilder<A> {
            docs![&spanned_ty.ty]
        }

        fn primitive_ty(&self, primitive_ty: &PrimitiveTy) -> DocBuilder<A> {
            match primitive_ty {
                PrimitiveTy::Bool => docs!["Bool"],
                PrimitiveTy::Int(int_kind) => docs![int_kind],
                PrimitiveTy::Float(_) => emit_error!(issue 1715, "Unsupported Float type"),
                PrimitiveTy::Char => docs!["Char"],
                PrimitiveTy::Str => docs!["String"],
            }
        }

        fn int_kind(&self, int_kind: &IntKind) -> DocBuilder<A> {
            docs![match (&int_kind.signedness, &int_kind.size) {
                (Signedness::Signed, IntSize::S8) => "i8",
                (Signedness::Signed, IntSize::S16) => "i16",
                (Signedness::Signed, IntSize::S32) => "i32",
                (Signedness::Signed, IntSize::S64) => "i64",
                (Signedness::Signed, IntSize::S128) => "i128",
                (Signedness::Signed, IntSize::SSize) => "isize",
                (Signedness::Unsigned, IntSize::S8) => "u8",
                (Signedness::Unsigned, IntSize::S16) => "u16",
                (Signedness::Unsigned, IntSize::S32) => "u32",
                (Signedness::Unsigned, IntSize::S64) => "u64",
                (Signedness::Unsigned, IntSize::S128) => "u128",
                (Signedness::Unsigned, IntSize::SSize) => "usize",
            }]
        }

        fn generic_value(&self, generic_value: &GenericValue) -> DocBuilder<A> {
            match generic_value {
                GenericValue::Ty(ty) => docs![ty],
                GenericValue::Expr(expr) => docs![expr],
                GenericValue::Lifetime => unreachable_by_invariant!(Drop_references),
            }
        }

        fn quote_content(&self, quote_content: &QuoteContent) -> DocBuilder<A> {
            match quote_content {
                QuoteContent::Verbatim(s) => {
                    intersperse!(s.lines().map(|x| x.to_string()), hardline!())
                }
                QuoteContent::Expr(expr) => docs![expr],
                QuoteContent::Pattern(pat) => docs![pat],
                QuoteContent::Ty(ty) => docs![ty],
            }
        }

        fn quote(&self, quote: &Quote) -> DocBuilder<A> {
            concat![&quote.0]
        }

        fn param(&self, param: &Param) -> DocBuilder<A> {
            self.pat_typed(&param.pat)
        }

        fn item(&self, Item { ident, kind, meta }: &Item) -> DocBuilder<A> {
            let body = match kind {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety: _,
                } => docs![
                    docs![
                        docs!["def", line!(), name].group(),
                        line!(),
                        generics,
                        params,
                        docs![": Result", line!(), &body.ty].group(),
                        line!(),
                        ":= do"
                    ]
                    .group(),
                    line!(),
                    body
                ]
                .group()
                .nest(INDENT),
                ItemKind::TyAlias {
                    name,
                    generics: _,
                    ty,
                } => docs!["abbrev ", name, reflow!(" := "), ty].group(),
                ItemKind::Use {
                    path: _,
                    is_external: _,
                    rename: _,
                } => nil!(),
                ItemKind::Quote { quote, origin: _ } => docs![quote],
                ItemKind::NotImplementedYet => {
                    emit_error!(issue 1706, "Item unsupported by the Hax engine (unimplemented yet)")
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    // TODO: use a resugaring, see https://github.com/cryspen/hax/issues/1668
                    if *is_struct {
                        // Structures
                        let Some(variant) = variants.first() else {
                            unreachable!(
                                "Structures should always have a constructor (even empty ones)"
                            )
                        };
                        let args = if !variant.is_record {
                            // Tuple-like structure, using positional arguments
                            intersperse!(
                                variant.arguments.iter().enumerate().map(|(i, (_, ty, _))| {
                                    docs![format!("_{i} :"), line!(), ty].group().nest(INDENT)
                                }),
                                hardline!()
                            )
                        } else {
                            // Structure-like structure, using named arguments
                            intersperse!(
                                variant.arguments.iter().map(|(id, ty, _)| {
                                    docs![self.render_last(id), reflow!(" : "), ty]
                                        .group()
                                        .nest(INDENT)
                                }),
                                hardline!()
                            )
                        };
                        docs![
                            docs![reflow!("structure "), name, line!(), generics, "where"].group(),
                            docs![hardline!(), args],
                        ]
                        .nest(INDENT)
                        .group()
                    } else {
                        // Enums
                        let applied_name: DocBuilder<A> = docs![name, line!(), generics].group();
                        docs![
                            docs!["inductive ", name, line!(), generics, ": Type"].group(),
                            hardline!(),
                            concat!(variants.iter().map(|variant| docs![
                                "| ",
                                docs![variant, applied_name.clone()].group().nest(INDENT),
                                hardline!()
                            ])),
                        ]
                    }
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    // Type parameters are also parameters of the class, but constraints are fields of the class
                    docs![
                        docs![
                            docs![reflow!("class "), name],
                            (!generics.params.is_empty()).then_some(docs![
                                line!(),
                                intersperse!(&generics.params, line!()).group()
                            ]),
                            line!(),
                            "where"
                        ]
                        .group(),
                        hardline!(),
                        (!generics.constraints.is_empty()).then_some(docs![zip_right!(
                            generics
                                .constraints
                                .iter()
                                .map(|constraint: &GenericConstraint| {
                                    match constraint {
                                        GenericConstraint::Type(tc_constraint) => docs![
                                            format!("_constr_{}", tc_constraint.name),
                                            " :",
                                            line!(),
                                            constraint
                                        ]
                                        .group()
                                            .brackets(),
                                        GenericConstraint::Lifetime(_) => unreachable_by_invariant!(Drop_references),
                                        GenericConstraint::Projection(_) => emit_error!(issue 1710, "Unsupported equality constraints on associated types"),
                                    }
                                }),
                            hardline!()
                        )]),
                        intersperse!(
                            items.iter().filter(|item| {
                                // TODO: should be treated directly by name rendering, see :
                                // https://github.com/cryspen/hax/issues/1646
                                !(item.ident.is_precondition() || item.ident.is_postcondition())
                            }),
                            hardline!()
                        )
                    ]
                    .nest(INDENT)
                }
                ItemKind::Impl {
                    generics,
                    self_ty: _,
                    of_trait: (trait_, args),
                    items,
                    parent_bounds: _,
                    safety: _,
                } => docs![
                    docs![
                        docs![reflow!("instance "), ident, line!(), generics, ":"].group(),
                        line!(),
                        docs![trait_, concat!(args.iter().map(|gv| docs![line!(), gv]))].group(),
                        line!(),
                        "where",
                    ]
                    .group()
                    .nest(INDENT),
                    docs![
                        hardline!(),
                        intersperse!(
                            items.iter().filter(|item| {
                                // TODO: should be treated directly by name rendering, see :
                                // https://github.com/cryspen/hax/issues/1646
                                !(item.ident.is_precondition() || item.ident.is_postcondition())
                            }),
                            hardline!()
                        )
                    ]
                    .nest(INDENT),
                ],
                ItemKind::Resugared(resugared_item_kind) => match resugared_item_kind {
                    ResugaredItemKind::Constant {
                        name,
                        body,
                        generics,
                    } => docs![
                        docs![
                            docs!["def", line!(), name].group(),
                            line!(),
                            generics,
                            docs![":", line!(), &body.ty].group(),
                            line!(),
                            ":="
                        ]
                        .group(),
                        line!(),
                        docs![
                            "Result.of_isOk",
                            line!(),
                            self.do_block(body).parens(),
                            line!(),
                            "(by rfl)"
                        ]
                        .group()
                        .nest(INDENT)
                    ]
                    .group()
                    .nest(INDENT),
                },
                ItemKind::Alias { .. } => {
                    // aliases are introduced when creating bundles. Those should not appear in
                    // Lean, as items can be named correctly in any file.
                    emit_error!(issue 1658, "Unsupported alias item")
                }
                ItemKind::Error(e) => docs![e],
            };
            docs![meta, body]
        }

        fn trait_item(
            &self,
            TraitItem {
                meta: _,
                kind,
                generics,
                ident,
            }: &TraitItem,
        ) -> DocBuilder<A> {
            let name = self.render_last(ident);
            docs![match kind {
                TraitItemKind::Fn(ty) => {
                    docs![name, softline!(), generics, ":", line!(), ty]
                        .group()
                        .nest(INDENT)
                }
                TraitItemKind::Type(constraints) => {
                    docs![
                        name.clone(),
                        reflow!(" : Type"),
                        concat!(constraints.iter().map(|c| docs![
                            hardline!(),
                            docs![
                                format!("_constr_{}", c.name),
                                reflow!(" :"),
                                line!(),
                                &c.goal
                            ]
                            .group()
                            .nest(INDENT)
                            .brackets()
                        ]))
                    ]
                }
                TraitItemKind::Default { .. } =>
                    emit_error!(issue 1707, "Unsupported default implementation for trait items"),
                TraitItemKind::Resugared(_) => {
                    unreachable!("This backend has no resugaring for trait items")
                }
            }]
        }

        fn impl_item(
            &self,
            ImplItem {
                meta: _,
                generics,
                kind,
                ident,
            }: &ImplItem,
        ) -> DocBuilder<A> {
            let name = self.render_last(ident);
            match kind {
                ImplItemKind::Type {
                    ty,
                    parent_bounds: _,
                } => docs![name, reflow!(" := "), ty],
                ImplItemKind::Fn { body, params } => docs![
                    docs![
                        name,
                        softline!(),
                        generics,
                        zip_right!(params, line!()).group(),
                        ":= do",
                    ]
                    .group(),
                    line!(),
                    body
                ]
                .group()
                .nest(INDENT),
                ImplItemKind::Resugared(_) => {
                    unreachable!("This backend has no resugaring for impl items")
                }
            }
        }

        fn impl_ident(&self, ImplIdent { goal, name: _ }: &ImplIdent) -> DocBuilder<A> {
            docs![goal]
        }

        fn trait_goal(&self, TraitGoal { trait_, args }: &TraitGoal) -> DocBuilder<A> {
            docs![trait_, concat!(args.iter().map(|arg| docs![line!(), arg]))]
                .parens()
                .nest(INDENT)
                .group()
        }

        fn variant(
            &self,
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            }: &Variant,
        ) -> DocBuilder<A> {
            docs![
                concat!(attributes),
                self.render_last(name),
                softline!(),
                // args
                if *is_record {
                    // Use named the arguments, keeping only the head of the identifier
                    docs![
                        intersperse!(
                            arguments.iter().map(|(id, ty, _)| {
                                docs![self.render_last(id), reflow!(" : "), ty]
                                    .parens()
                                    .group()
                            }),
                            line!()
                        )
                        .align()
                        .nest(INDENT),
                        line!(),
                        reflow!(": "),
                    ]
                    .group()
                } else {
                    // Use anonymous arguments
                    docs![
                        reflow!(": "),
                        concat!(
                            arguments
                                .iter()
                                .map(|(_, ty, _)| { docs![ty, reflow!(" -> ")] })
                        )
                    ]
                }
            ]
            .group()
            .nest(INDENT)
        }

        fn symbol(&self, symbol: &Symbol) -> DocBuilder<A> {
            docs![self.escape(symbol.to_string())]
        }

        fn metadata(
            &self,
            Metadata {
                span: _,
                attributes,
            }: &Metadata,
        ) -> DocBuilder<A> {
            concat!(attributes)
        }

        fn lhs(&self, _lhs: &Lhs) -> DocBuilder<A> {
            unreachable_by_invariant!(Local_mutation)
        }

        fn safety_kind(&self, _safety_kind: &SafetyKind) -> DocBuilder<A> {
            nil!()
        }

        fn binding_mode(&self, _binding_mode: &BindingMode) -> DocBuilder<A> {
            unreachable!("This backend handle binding modes directly inside patterns")
        }

        fn region(&self, _region: &Region) -> DocBuilder<A> {
            unreachable_by_invariant!(Drop_references)
        }

        fn float_kind(&self, _float_kind: &FloatKind) -> DocBuilder<A> {
            emit_error!(issue 1715, "floats are unsupported")
        }

        fn dyn_trait_goal(&self, _dyn_trait_goal: &DynTraitGoal) -> DocBuilder<A> {
            emit_error!(issue 1708, "`dyn` traits are unsupported")
        }

        fn attribute(&self, Attribute { kind, span: _ }: &Attribute) -> DocBuilder<A> {
            match kind {
                AttributeKind::Tool { .. } => {
                    nil!()
                }
                AttributeKind::DocComment {
                    kind: DocCommentKind::Line,
                    body,
                } => comment!(body.clone()).append(hardline!()),
                AttributeKind::DocComment {
                    kind: DocCommentKind::Block,
                    body,
                } => docs![
                    "/--",
                    line!(),
                    intersperse!(body.lines().map(|line| line.to_string()), line!()),
                    line!(),
                    "-/"
                ]
                .nest(INDENT)
                .group()
                .append(hardline!()),
            }
        }

        fn borrow_kind(&self, _borrow_kind: &BorrowKind) -> DocBuilder<A> {
            unreachable_by_invariant!(Drop_references)
        }

        fn guard(&self, _guard: &Guard) -> DocBuilder<A> {
            unreachable_by_invariant!(Drop_match_guards)
        }

        fn projection_predicate(
            &self,
            _projection_predicate: &ProjectionPredicate,
        ) -> DocBuilder<A> {
            emit_error!(issue 1710, "Projection predicate (type equalities on associated types) are unsupported")
        }

        fn error_node(&self, _error_node: &ErrorNode) -> DocBuilder<A> {
            // TODO : Should be made unreachable by https://github.com/cryspen/hax/pull/1672
            text!("sorry")
        }

        // Impl expressions

        fn impl_expr(&self, _impl_expr: &ImplExpr) -> DocBuilder<A> {
            emit_error!(issue 1716, "Explicit impl expressions are unsupported")
        }
    }
};
