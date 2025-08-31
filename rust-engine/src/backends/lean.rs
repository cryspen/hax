//! The Lean backend
//!
//! This module defines the trait implementations to export the rust ast to
//! Pretty::Doc type, which can in turn be exported to string (or, eventually,
//! source maps).

use std::cell::LazyCell;
use std::collections::HashSet;

use super::prelude::*;
use crate::{
    ast::identifiers::global_id::view::{ConstructorKind, PathSegment, TypeDefKind},
    printer::pretty_ast::DebugJSON,
    resugarings::BinOp,
};

mod binops {
    pub use crate::names::rust_primitives::hax::machine_int::{add, div, mul, rem, shr, sub};
    pub use crate::names::rust_primitives::hax::{logical_op_and, logical_op_or};
}

/// The Lean printer
#[derive(Default)]
pub struct LeanPrinter {}
impl_doc_allocator_for!(LeanPrinter);

const INDENT: isize = 2;

const RESERVED_KEYWORDS: LazyCell<HashSet<String>> = LazyCell::new(|| {
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
                    if let Some(parent) = chunk.parent() {
                        Some(vec![
                            self.render_path_segment_payload(parent.payload())
                                .to_string(),
                            self.escape(
                                self.render_path_segment_payload(chunk.payload())
                                    .to_string(),
                            ),
                        ])
                    } else {
                        None
                    }
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
        vec![Box::new(BinOp::new(&[
            binops::add(),
            binops::sub(),
            binops::mul(),
            binops::rem(),
            binops::div(),
            binops::shr(),
            binops::logical_op_and(),
            binops::logical_op_or(),
        ]))]
    }

    const NAME: &str = "Lean";
}

/// The Lean backend
pub struct LeanBackend;

impl Backend for LeanBackend {
    type Printer = LeanPrinter;

    fn module_path(&self, module: &Module) -> camino::Utf8PathBuf {
        camino::Utf8PathBuf::from_iter(
            self.printer()
                .render_strings(&module.ident.as_concrete().unwrap().view()),
        )
        .with_extension("lean")
    }
}

impl LeanPrinter {
    /// A filter for items blacklisted by the Lean backend : returns false if
    /// the item is definitely not printable, but might return true on
    /// unsupported items
    pub fn printable_item(item: &Item) -> bool {
        match &item.kind {
            // Anonymous consts
            ItemKind::Fn {
                name,
                generics: _,
                body: _,
                params: _,
                safety: _,
            } if name.is_empty() => false,
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
    /// and projector ids
    pub fn render_id(&self, id: &GlobalId) -> String {
        match id {
            GlobalId::Concrete(concrete_id) | GlobalId::Projector(concrete_id) => {
                self.render_string(&concrete_id.view())
            }
        }
    }

    /// Escapes local identifiers (prefixing reserved keywords with an underscore)
    pub fn escape(&self, id: String) -> String {
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
            .render(
                &id.as_concrete()
                    .expect("Rendering a projector as a constructor")
                    .view(),
            )
            .path
            .last()
            .expect("Segments should always be non-empty")
            .clone();
        self.escape(id)
    }

    /// Prints the fields of a constructor (struct or variant of an enum)
    pub fn fields<'a, 'b, A: 'a + Clone>(
        &'a self,
        fields: &Vec<(GlobalId, Expr)>,
        is_record: &bool,
    ) -> DocBuilder<'a, Self, A> {
        install_pretty_helpers!(self: LeanPrinter);
        #[allow(unused)]
        macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}
        if *is_record {
            // Record fields (named arguments)
            docs![intersperse!(
                fields.iter().map(|(id, e)| {
                    docs![self.render_last(id), reflow!(" := "), e]
                        .parens()
                        .group()
                }),
                line!()
            )]
            .group()
        } else {
            // Tuple fields (positional arguments)
            docs![intersperse!(fields.iter().map(|(_, e)| e), line!())]
        }
    }

    /// Renders expressions with an explicit ascription `(e : ty)`. Used for numeric literals (to
    /// prevent incorrect inference), etc.
    fn expr_typed<'a, 'b, A: 'a + Clone>(&'a self, expr: &'b Expr) -> DocBuilder<'a, Self, A> {
        install_pretty_helpers!(self: Self);
        docs![expr.kind(), reflow!(" : "), expr.ty.kind()]
            .parens()
            .group()
    }

    /// Renders expressions with an explicit ascription `(e : Result ty)`. Used for the body of closure, for
    /// numeric literals, etc.
    fn expr_typed_result<'a, 'b, A: 'a + Clone>(
        &'a self,
        expr: &'b Expr,
    ) -> DocBuilder<'a, Self, A> {
        macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}
        install_pretty_helpers!(self: Self);
        docs![
            expr.kind(),
            reflow!(" : "),
            docs!["Result", line!(), expr.ty.kind()].group()
        ]
        .parens()
        .group()
    }
}

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
const _: () = {
    // Boilerplate: define local macros to disambiguate otherwise `std` macros.
    #[allow(unused)]
    macro_rules! todo {($($tt:tt)*) => {disambiguated_todo!($($tt)*)};}
    #[allow(unused)]
    macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}
    #[allow(unused)]
    macro_rules! concat {($($tt:tt)*) => {disambiguated_concat!($($tt)*)};}

    impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for LeanPrinter {
        fn module(&'a self, module: &'b Module) -> DocBuilder<'a, Self, A> {
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

        fn global_id(&'a self, global_id: &'b GlobalId) -> DocBuilder<'a, Self, A> {
            docs![self.render_id(global_id)]
        }

        /// Render generics, adding a space after each parameter
        fn generics(&'a self, generics: &'b Generics) -> DocBuilder<'a, Self, A> {
            // TODO : do not ignore constraints
            concat!(generics.params.iter().map(|param| {
                match param.kind {
                    GenericParamKind::Lifetime => unreachable!(),
                    GenericParamKind::Type => docs![param, reflow!(" : Type")]
                        .parens()
                        .group()
                        .append(line!()),
                    GenericParamKind::Const { .. } => {
                        todo!("-- to debug const param run: {}", DebugJSON(param))
                    }
                }
            }))
            .group()
        }

        fn expr(&'a self, expr: &'b Expr) -> DocBuilder<'a, Self, A> {
            match *expr.kind {
                ExprKind::Literal(Literal::Int { .. }) => self.expr_typed(expr),
                _ => docs![expr.kind()],
            }
        }

        fn pat(&'a self, pat: &'b Pat) -> DocBuilder<'a, Self, A> {
            docs![&*pat.kind, reflow!(" : "), &pat.ty].parens().group()
        }

        fn expr_kind(&'a self, expr_kind: &'b ExprKind) -> DocBuilder<'a, Self, A> {
            match expr_kind {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    if let Some(else_branch) = else_ {
                        docs![
                            docs!["if", line!(), condition].group(),
                            line!(),
                            docs!["then", line!(), then].group().nest(INDENT),
                            line!(),
                            docs!["else", line!(), else_branch].group().nest(INDENT)
                        ]
                        .group()
                    } else {
                        // The Hax engine should ensure that there is always an else branch
                        unreachable!()
                    }
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls: _,
                    trait_: _,
                } => {
                    let monadic_lift = if let ExprKind::GlobalId(head_id) = head.kind()
                        && (head_id.is_constructor() || head_id.is_field())
                    {
                        None
                    } else {
                        Some("← ")
                    };
                    let generic_args = (!generic_args.is_empty()).then_some(
                        docs![
                            line!(),
                            self.intersperse(generic_args, line!()).nest(INDENT)
                        ]
                        .group(),
                    );
                    let args = (!args.is_empty()).then_some(
                        docs![line!(), intersperse!(args, line!()).nest(INDENT)].group(),
                    );
                    docs![monadic_lift, head, generic_args, args]
                        .parens()
                        .group()
                }
                ExprKind::Literal(literal) => docs![literal],
                ExprKind::Array(exprs) => docs![
                    "#v[",
                    intersperse!(exprs, docs![",", line!()])
                        .nest(INDENT)
                        .group(),
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
                    } else {
                        docs![constructor, line!(), self.fields(fields, is_record)]
                            .parens()
                            .group()
                    }
                }
                ExprKind::Let { lhs, rhs, body } => docs![
                    docs![
                        "let",
                        line!(),
                        lhs,
                        line!(),
                        "← ",
                        docs!["pure", line!(), rhs].parens().group(),
                        ";"
                    ]
                    .nest(INDENT)
                    .group(),
                    line!(),
                    body,
                ],
                ExprKind::GlobalId(global_id) => docs![global_id],
                ExprKind::LocalId(local_id) => docs![local_id],
                ExprKind::Ascription { e, ty } => docs![
                    // This insertion should be done by a monadic phase (or resugaring). See
                    // https://github.com/cryspen/hax/issues/1620
                    match *e.kind {
                        ExprKind::Literal(_) | ExprKind::Construct { .. } => None,
                        _ => Some("← "),
                    },
                    e,
                    reflow!(" : "),
                    ty
                ]
                .parens()
                .group(),
                ExprKind::Closure {
                    params,
                    body,
                    captures: _,
                } => docs![
                    reflow!("fun "),
                    intersperse!(params, softline!()).group(),
                    reflow!(" => do"),
                    line!(),
                    self.expr_typed_result(body)
                ]
                .parens()
                .group()
                .nest(INDENT),
                ExprKind::Resugared(resugared_expr_kind) => match resugared_expr_kind {
                    ResugaredExprKind::BinOp {
                        op,
                        lhs,
                        rhs,
                        generic_args: _,
                        bounds_impls: _,
                        trait_: _,
                    } => {
                        let symbol = if op == &binops::add() {
                            "+?"
                        } else if op == &binops::sub() {
                            "-?"
                        } else if op == &binops::mul() {
                            "*?"
                        } else if op == &binops::div() {
                            "/?"
                        } else if op == &binops::rem() {
                            "%?"
                        } else if op == &binops::shr() {
                            ">>>?"
                        } else if op == &binops::logical_op_and() {
                            "&&?"
                        } else if op == &binops::logical_op_or() {
                            "||?"
                        } else {
                            unreachable!()
                        };
                        // This monad lifting should be handled by a phase/resugaring, see
                        // https://github.com/cryspen/hax/issues/1620
                        docs!["← ", lhs, softline!(), symbol, softline!(), rhs]
                            .group()
                            .parens()
                    }
                },
                ExprKind::Match { scrutinee, arms } => docs![
                    docs!["match", line!(), scrutinee, reflow!(" with")].group(),
                    line!(),
                    intersperse!(arms, line!())
                ]
                .parens()
                .nest(INDENT)
                .group(),
                _ => todo!(),
            }
        }

        fn arm(&'a self, arm: &'b Arm) -> DocBuilder<'a, Self, A> {
            if let Some(_guard) = &arm.guard {
                todo!()
            } else {
                docs!["| ", &*arm.pat.kind, reflow!(" => "), &arm.body].group()
            }
        }

        fn pat_kind(&'a self, pat_kind: &'b PatKind) -> DocBuilder<'a, Self, A> {
            match pat_kind {
                PatKind::Wild => docs!["_"],
                PatKind::Ascription { pat, ty: _ } => docs![pat],
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => match (mutable, mode, sub_pat) {
                    (false, BindingMode::ByValue, None) => docs![var],
                    _ => panic!(),
                },
                PatKind::Or { sub_pats } => docs![intersperse!(sub_pats, reflow!(" | "))].group(),
                PatKind::Array { args: _ } => todo!(),
                PatKind::Deref { sub_pat: _ } => todo!(),
                PatKind::Constant { lit: _ } => todo!(),
                PatKind::Construct {
                    constructor: _,
                    is_record,
                    is_struct,
                    fields,
                } if *is_struct => {
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
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    if *is_record {
                        docs![
                            constructor,
                            line!(),
                            intersperse!(
                                fields.iter().map(|(id, e)| {
                                    docs![self.render_last(id), reflow!(" := "), e]
                                        .parens()
                                        .group()
                                }),
                                line!()
                            )
                            .align()
                            .group()
                        ]
                        .parens()
                        .group()
                        .nest(INDENT)
                    } else {
                        docs![
                            constructor,
                            line!(),
                            intersperse!(fields.iter().map(|(_, e)| docs![e]), line!())
                        ]
                        .parens()
                        .group()
                    }
                }
                PatKind::Resugared(_resugared_pat_kind) => todo!(),
                PatKind::Error(_error_node) => todo!(),
            }
        }

        fn ty(&'a self, ty: &'b Ty) -> DocBuilder<'a, Self, A> {
            docs![ty.kind()]
        }

        fn ty_kind(&'a self, ty_kind: &'b TyKind) -> DocBuilder<'a, Self, A> {
            match ty_kind {
                TyKind::Primitive(primitive_ty) => docs![primitive_ty],
                TyKind::Tuple(items) => intersperse!(items, reflow![" * "]).parens().group(),
                TyKind::App { head, args } => {
                    if args.is_empty() {
                        docs![head]
                    } else {
                        docs![head, softline!(), intersperse!(args, softline!())]
                            .parens()
                            .group()
                    }
                }
                TyKind::Arrow { inputs, output } => docs![
                    concat![inputs.iter().map(|input| docs![input, reflow!(" -> ")])],
                    "Result ",
                    output
                ],
                TyKind::Param(local_id) => docs![local_id],
                TyKind::Slice(ty) => docs!["RustSlice", line!(), ty].parens().group(),
                TyKind::Array { ty, length } => {
                    docs!["RustArray", line!(), ty, line!(), &(**length)]
                        .parens()
                        .group()
                }
                _ => todo!(),
            }
        }

        fn literal(&'a self, literal: &'b Literal) -> DocBuilder<'a, Self, A> {
            docs![match literal {
                Literal::String(symbol) => format!("\"{symbol}\""),
                Literal::Char(c) => format!("'{c}'"),
                Literal::Bool(b) => format!("{b}"),
                Literal::Int {
                    value,
                    negative,
                    kind: _,
                } => format!("{}{value}", if *negative { "-" } else { "" }),
                Literal::Float {
                    value: _,
                    negative: _,
                    kind: _,
                } => todo!(),
            }]
        }

        fn local_id(&'a self, local_id: &'b LocalId) -> DocBuilder<'a, Self, A> {
            docs![self.escape(local_id.0.to_string())]
        }

        fn spanned_ty(&'a self, spanned_ty: &'b SpannedTy) -> DocBuilder<'a, Self, A> {
            docs![&spanned_ty.ty]
        }

        fn primitive_ty(&'a self, primitive_ty: &'b PrimitiveTy) -> DocBuilder<'a, Self, A> {
            match primitive_ty {
                PrimitiveTy::Bool => docs!["Bool"],
                PrimitiveTy::Int(int_kind) => docs![int_kind],
                PrimitiveTy::Float(_float_kind) => todo!(),
                PrimitiveTy::Char => docs!["Char"],
                PrimitiveTy::Str => docs!["String"],
            }
        }

        fn int_kind(&'a self, int_kind: &'b IntKind) -> DocBuilder<'a, Self, A> {
            docs![match (&int_kind.signedness, &int_kind.size) {
                (Signedness::Signed, IntSize::S8) => "Int8",
                (Signedness::Signed, IntSize::S16) => "Int16",
                (Signedness::Signed, IntSize::S32) => "Int32",
                (Signedness::Signed, IntSize::S64) => "Int64",
                (Signedness::Signed, IntSize::S128) => todo!(),
                (Signedness::Signed, IntSize::SSize) => "ISize",
                (Signedness::Unsigned, IntSize::S8) => "UInt8",
                (Signedness::Unsigned, IntSize::S16) => "UInt16",
                (Signedness::Unsigned, IntSize::S32) => "UInt32",
                (Signedness::Unsigned, IntSize::S64) => "UInt64",
                (Signedness::Unsigned, IntSize::S128) => todo!(),
                (Signedness::Unsigned, IntSize::SSize) => "USize",
            }]
        }

        fn generic_value(&'a self, generic_value: &'b GenericValue) -> DocBuilder<'a, Self, A> {
            match generic_value {
                GenericValue::Ty(ty) => docs![ty],
                GenericValue::Expr(expr) => docs![expr],
                GenericValue::Lifetime => todo!(),
            }
        }

        fn quote_content(&'a self, quote_content: &'b QuoteContent) -> DocBuilder<'a, Self, A> {
            match quote_content {
                QuoteContent::Verbatim(s) => {
                    intersperse!(s.lines().map(|x| x.to_string()), hardline!())
                }
                QuoteContent::Expr(expr) => docs![expr],
                QuoteContent::Pattern(pat) => docs![pat],
                QuoteContent::Ty(ty) => docs![ty],
            }
        }

        fn quote(&'a self, quote: &'b Quote) -> DocBuilder<'a, Self, A> {
            concat![&quote.0]
        }

        fn param(&'a self, param: &'b Param) -> DocBuilder<'a, Self, A> {
            docs![&param.pat]
        }

        fn generic_param(&'a self, generic_param: &'b GenericParam) -> DocBuilder<'a, Self, A> {
            docs![&generic_param.ident]
        }

        fn item_kind(&'a self, item_kind: &'b ItemKind) -> DocBuilder<'a, Self, A> {
            match item_kind {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety: _,
                } => match &*body.kind {
                    // Literal consts. This should be done by a resugaring, see
                    // https://github.com/cryspen/hax/issues/1614
                    ExprKind::Literal(l) if params.is_empty() => {
                        docs!["def ", name, reflow!(" : "), &body.ty, reflow!(" := "), l].group()
                    }
                    _ => {
                        let generics = (!generics.params.is_empty()).then_some(
                            docs![
                                line!(),
                                intersperse!(&generics.params, softline!()).braces().group()
                            ]
                            .group(),
                        );
                        let args = (!params.is_empty())
                            .then_some(docs![line!(), intersperse!(params, softline!())].group());
                        docs![
                            "def ",
                            name,
                            generics,
                            args,
                            docs![line!(), ": ", docs!["Result ", &body.ty].group()].group(),
                            " := do",
                            line!(),
                            docs![&*body.kind].group()
                        ]
                        .group()
                        .nest(INDENT)
                    }
                },
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
                    docs!["example : Unit := sorry /- unsupported by the Hax engine -/"]
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    if *is_struct {
                        // Structures
                        let Some(variant) = variants.first() else {
                            // Structures always have a constructor (even empty ones)
                            unreachable!()
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
                        let generics = (!generics.params.is_empty()).then_some(
                            concat![generics.params.iter().map(|param| docs![param, line!()])]
                                .group(),
                        );
                        docs![
                            docs!["structure ", name, line!(), generics, "where"].group(),
                            docs![hardline!(), args].nest(INDENT),
                        ]
                        .group()
                    } else {
                        // Enums
                        let applied_name: DocBuilder<'a, Self, A> = docs![
                            name,
                            concat!(generics.params.iter().map(|param| match param.kind {
                                GenericParamKind::Type => docs![line!(), param],
                                _ => nil!(),
                            }))
                        ]
                        .group();
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
                _ => todo!("-- to debug missing item run: {}", DebugJSON(item_kind)),
            }
        }

        fn item(&'a self, item: &'b Item) -> DocBuilder<'a, Self, A> {
            if LeanPrinter::printable_item(item) {
                docs![item.kind()]
            } else {
                nil!()
            }
        }

        fn variant(&'a self, variant: &'b Variant) -> DocBuilder<'a, Self, A> {
            docs![
                self.render_last(&variant.name),
                softline!(),
                if variant.is_record {
                    // Use named the arguments, keeping only the head of the identifier
                    docs![
                        intersperse!(
                            variant.arguments.iter().map(|(id, ty, _)| {
                                docs![self.render_last(id), reflow!(" : "), ty]
                                    .parens()
                                    .group()
                            }),
                            line!()
                        )
                        .align()
                        .nest(INDENT),
                        reflow!(" : ")
                    ]
                } else {
                    // Use anonymous arguments
                    docs![
                        reflow!(" : "),
                        concat!(
                            variant
                                .arguments
                                .iter()
                                .map(|(_, ty, _)| { docs![ty, reflow!(" -> ")] })
                        )
                    ]
                }
            ]
            .group()
            .nest(INDENT)
        }
    }
};
