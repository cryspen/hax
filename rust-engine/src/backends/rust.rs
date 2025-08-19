//! A Rust backend (and printer) for hax.

use super::prelude::*;

/// The Rust printer.
#[derive(Default, Clone)]
pub struct RustPrinter;
impl_doc_allocator_for!(RustPrinter);

impl Printer for RustPrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![]
    }

    const NAME: &str = "Rust";
}

/// The Rust backend.
pub struct RustBackend;

impl Backend for RustBackend {
    type Printer = RustPrinter;

    fn module_path(&self, _module: &Module) -> camino::Utf8PathBuf {
        // TODO: dummy path for now, until we have GlobalId rendering (see #1599).
        camino::Utf8PathBuf::from("dummy.rs")
    }
}

const INDENT: isize = 4;

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
// Note: the `const` wrapping makes my IDE and LSP happy. Otherwise, I don't get
// autocompletion of methods in the impl block below.
const _: () = {
    macro_rules! todo {
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

    macro_rules! sep {
        ($l:expr, $it:expr, $r:expr, $sep:expr$(,)?) => {
            docs![
                intersperse!($it, docs![$sep, line!()]),
                docs![","].flat_alt(nil!())
            ]
            .enclose(line_!(), line_!())
            .nest(INDENT)
            .enclose($l, $r)
            .group()
        };
        ($l:expr, $it:expr, $r:expr$(,)?) => {
            sep!($l, $it, $r, ",")
        };
    }

    macro_rules! sep_opt {
        (@$l:expr, $it:expr, $($rest:tt)*) => {
            {
                let mut it = $it.into_iter().peekable();
                if it.peek().is_some() {
                    sep!($l, it, $($rest)*)
                } else {
                    nil!()
                }
            }
        };
        ($l:expr, $it:expr, $($rest:tt)*) => {
            sep_opt!(@$l, $it, $($rest)*)
        };
    }

    impl<'a, 'b> RustPrinter {
        fn generic_params<A: Clone + 'a>(
            &'a self,
            generic_params: &'b [GenericParam],
        ) -> pretty::DocBuilder<'a, Self, A> {
            sep_opt!("<", generic_params, ">")
        }
        fn where_clause<A: Clone + 'a>(
            &'a self,
            constraints: &'b [GenericConstraint],
        ) -> pretty::DocBuilder<'a, Self, A> {
            if constraints.is_empty() {
                return nil!();
            }
            docs![
                line!(),
                "where",
                line!(),
                intersperse!(constraints, docs![",", line!()])
                    .nest(INDENT)
                    .group(),
                line!(),
            ]
            .nest(INDENT)
            .group()
        }
        fn attributes<A: Clone + 'a>(
            &'a self,
            attrs: &'b [Attribute],
        ) -> pretty::DocBuilder<'a, Self, A> {
            concat!(
                attrs
                    .iter()
                    .filter(|attr| match &attr.kind {
                        AttributeKind::Tool { .. } => false,
                        AttributeKind::DocComment { .. } => true,
                    })
                    .map(|attr| docs![attr, hardline!()])
            )
        }
    }

    impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for RustPrinter {
        fn module(&'a self, module: &'b Module) -> DocBuilder<'a, Self, A> {
            intersperse!(&module.items, docs![hardline!(), hardline!()])
        }

        fn safety_kind(&'a self, safety_kind: &'b SafetyKind) -> pretty::DocBuilder<'a, Self, A> {
            match safety_kind {
                SafetyKind::Safe => nil!(),
                SafetyKind::Unsafe => docs![text!("unsafe"), space!()],
            }
        }
        fn param(&'a self, param: &'b Param) -> pretty::DocBuilder<'a, Self, A> {
            docs![&param.pat, ":", space!(), &param.ty]
        }
        fn binding_mode(
            &'a self,
            binding_mode: &'b BindingMode,
        ) -> pretty::DocBuilder<'a, Self, A> {
            match binding_mode {
                BindingMode::ByRef(BorrowKind::Mut) => docs!["mut", space!()],
                _ => nil!(),
            }
        }
        fn pat(&'a self, pat: &'b Pat) -> pretty::DocBuilder<'a, Self, A> {
            match &*pat.kind {
                PatKind::Wild => docs!["_"],
                PatKind::Ascription { pat, ty } => docs![pat, ":", space!(), ty],
                PatKind::Or { sub_pats } => {
                    intersperse!(sub_pats, docs![line!(), "|", line!()])
                }
                PatKind::Array { args } => sep!("[", args, "]", "|"),
                PatKind::Deref { sub_pat } => todo!(),
                PatKind::Constant { lit } => todo!(),
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    docs![
                        if *mutable {
                            docs!["mut", space!()]
                        } else {
                            nil!()
                        },
                        mode,
                        var,
                        sub_pat.as_ref().map(|pat| docs!["@", docs![pat]]),
                    ]
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => todo!(),
                PatKind::Resugared(resugared_pat_kind) => todo!(),
                PatKind::Error(error_node) => todo!(),
            }
        }
        fn primitive_ty(
            &'a self,
            primitive_ty: &'b PrimitiveTy,
        ) -> pretty::DocBuilder<'a, Self, A> {
            match primitive_ty {
                PrimitiveTy::Bool => todo!(),
                PrimitiveTy::Int(int_kind) => docs![int_kind],
                PrimitiveTy::Float(float_kind) => todo!(),
                PrimitiveTy::Char => todo!(),
                PrimitiveTy::Str => todo!(),
            }
        }
        fn signedness(
            &'a self,
            signedness: &'b literals::Signedness,
        ) -> pretty::DocBuilder<'a, Self, A> {
            match signedness {
                literals::Signedness::Signed => docs!["i"],
                literals::Signedness::Unsigned => docs!["u"],
            }
        }
        fn int_size(&'a self, int_size: &'b literals::IntSize) -> pretty::DocBuilder<'a, Self, A> {
            docs![match int_size {
                literals::IntSize::S8 => "8",
                literals::IntSize::S16 => "16",
                literals::IntSize::S32 => "32",
                literals::IntSize::S64 => "64",
                literals::IntSize::S128 => "128",
                literals::IntSize::SSize => "size",
            }]
        }
        fn generic_param(
            &'a self,
            generic_param: &'b GenericParam,
        ) -> pretty::DocBuilder<'a, Self, A> {
            docs![
                match &generic_param.kind {
                    GenericParamKind::Const { .. } => docs!["const", space!()],
                    _ => nil!(),
                },
                &generic_param.ident,
                match &generic_param.kind {
                    GenericParamKind::Const { ty } => docs![":", space!(), ty],
                    _ => nil!(),
                }
            ]
        }
        fn generic_constraint(
            &'a self,
            generic_constraint: &'b GenericConstraint,
        ) -> pretty::DocBuilder<'a, Self, A> {
            match generic_constraint {
                GenericConstraint::Lifetime(s) => docs![s.clone()],
                GenericConstraint::Type(impl_ident) => docs![impl_ident],
                GenericConstraint::Projection(projection_predicate) => docs![projection_predicate],
            }
        }
        fn impl_ident(&'a self, impl_ident: &'b ImplIdent) -> pretty::DocBuilder<'a, Self, A> {
            let trait_goal = &impl_ident.goal;
            let [self_ty, args @ ..] = &trait_goal.args[..] else {
                panic!()
            };
            docs![
                self_ty,
                space!(),
                ":",
                space!(),
                &trait_goal.trait_,
                sep_opt!("<", args, ">"),
            ]
        }
        fn ty(&'a self, ty: &'b Ty) -> pretty::DocBuilder<'a, Self, A> {
            match ty.kind() {
                TyKind::Primitive(primitive_ty) => docs![primitive_ty],
                TyKind::Tuple(items) => intersperse!(items, docs![",", line!()])
                    .nest(INDENT)
                    .group(),
                TyKind::App { head, args } => docs![head, sep_opt!("<", args, ">")],
                TyKind::Arrow { inputs, output } => todo!(),
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => docs![
                    "&",
                    if *mutable {
                        docs!["mut", space!()]
                    } else {
                        nil!()
                    },
                    inner
                ],
                TyKind::Param(local_id) => docs![local_id],
                TyKind::Slice(ty) => docs![ty].enclose("[", "]"),
                TyKind::Array { ty, length } => todo!(),
                TyKind::RawPointer => todo!(),
                TyKind::AssociatedType { impl_, item } => todo!(),
                TyKind::Opaque(global_id) => docs![global_id],
                TyKind::Dyn(dyn_trait_goals) => docs![
                    "dyn",
                    docs![
                        line!(),
                        intersperse!(dyn_trait_goals, docs![line!(), "+", space!()])
                    ]
                    .group()
                    .hang(0)
                ],
                TyKind::Resugared(resugared_ty_kind) => todo!(),
                TyKind::Error(error_node) => todo!(),
            }
        }
        fn literal(&'a self, literal: &'b literals::Literal) -> pretty::DocBuilder<'a, Self, A> {
            match literal {
                literals::Literal::String(symbol) => docs![symbol],
                literals::Literal::Char(ch) => text!(format!("{}", ch)),
                literals::Literal::Bool(b) => text!(format!("{}", b)),
                literals::Literal::Int {
                    value,
                    negative,
                    kind,
                } => docs![if *negative { docs!["-"] } else { nil!() }, value, kind],
                literals::Literal::Float {
                    value,
                    negative,
                    kind,
                } => todo!(),
            }
        }
        fn int_kind(&'a self, int_kind: &'b literals::IntKind) -> pretty::DocBuilder<'a, Self, A> {
            docs![&int_kind.signedness, &int_kind.size]
        }
        fn trait_goal(&'a self, trait_goal: &'b TraitGoal) -> pretty::DocBuilder<'a, Self, A> {
            let [self_ty, args @ ..] = &trait_goal.args[..] else {
                panic!()
            };
            docs![
                self_ty,
                space!(),
                "as",
                space!(),
                &trait_goal.trait_,
                sep_opt!("<", args, ">"),
            ]
            .enclose("<", ">")
        }
        fn generic_value(
            &'a self,
            generic_value: &'b GenericValue,
        ) -> pretty::DocBuilder<'a, Self, A> {
            match generic_value {
                GenericValue::Ty(ty) => docs![ty],
                GenericValue::Expr(expr) => docs![expr],
                GenericValue::Lifetime => docs!["'_"],
            }
        }
        fn expr(&'a self, expr: &'b Expr) -> pretty::DocBuilder<'a, Self, A> {
            match &*expr.kind {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => docs![
                    "if",
                    space!(),
                    docs![condition].parens(),
                    docs![then].braces(),
                    "else",
                    else_
                        .as_ref()
                        .map(|doc| docs![doc].braces())
                        .unwrap_or(nil!())
                ],
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls: _,
                    trait_,
                } => docs![
                    head,
                    trait_
                        .iter()
                        .map(|(ii, _generic_values)| docs![&ii.goal])
                        .next()
                        .unwrap_or(nil!()),
                    sep_opt!("<", generic_args, ">"),
                    sep!("(", args, ")")
                ],
                ExprKind::Literal(literal) => docs![literal],
                ExprKind::Array(exprs) => sep!("[", exprs, "]"),
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let payload = fields.iter().map(|(id, value)| {
                        docs![
                            if *is_record {
                                docs![id, ":", space!()]
                            } else {
                                nil!()
                            },
                            value
                        ]
                    });
                    docs![
                        constructor,
                        if *is_record {
                            sep!("{", payload, "}")
                        } else {
                            sep!("(", payload, ")")
                        }
                    ]
                }
                ExprKind::Match { scrutinee, arms } => {
                    docs!["match", scrutinee, sep!("{", arms, "}")]
                }
                ExprKind::Tuple(exprs) => todo!(),
                ExprKind::Borrow { mutable, inner } => todo!(),
                ExprKind::AddressOf { mutable, inner } => todo!(),
                ExprKind::Deref(expr) => todo!(),
                ExprKind::Let { lhs, rhs, body } => docs![
                    "let",
                    space!(),
                    lhs,
                    space!(),
                    "=",
                    docs![line!(), rhs].group().nest(INDENT),
                    ";",
                    hardline!(),
                    body
                ],
                ExprKind::GlobalId(global_id) => docs![global_id],
                ExprKind::LocalId(local_id) => docs![local_id],
                ExprKind::Ascription { e, ty } => docs![e, ":", space!(), ty].parens(),
                ExprKind::Assign { lhs, value } => docs![lhs, space!(), "=", space!(), value],
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => todo!(),
                ExprKind::Break { value, label } => docs!["break", space!(), value],
                ExprKind::Return { value } => docs!["return", space!(), value],
                ExprKind::Continue { label } => docs!["continue"],
                ExprKind::Closure {
                    params,
                    body,
                    captures: _,
                } => docs![
                    intersperse!(params, docs![",", space!()]).enclose("|", "|"),
                    body
                ],
                ExprKind::Block { body, safety_mode } => {
                    docs![
                        safety_mode,
                        docs![line_!(), body, line_!()]
                            .group()
                            .braces()
                            .nest(INDENT)
                    ]
                }
                ExprKind::Quote { contents } => todo!(),
                ExprKind::Resugared(resugared_expr_kind) => todo!(),
                ExprKind::Error(error_node) => todo!(),
            }
        }
        fn lhs(&'a self, lhs: &'b Lhs) -> pretty::DocBuilder<'a, Self, A> {
            match lhs {
                Lhs::LocalVar { var, ty: _ } => docs![var],
                Lhs::ArbitraryExpr(expr) => docs![std::ops::Deref::deref(expr)],
                Lhs::FieldAccessor { e, ty: _, field } => {
                    docs![std::ops::Deref::deref(e), ".", field]
                }
                Lhs::ArrayAccessor { e, ty: _, index } => {
                    docs![std::ops::Deref::deref(e), docs!(index).enclose("[", "]")]
                }
            }
        }
        fn global_id(
            &'a self,
            global_id: &'b identifiers::GlobalId,
        ) -> pretty::DocBuilder<'a, Self, A> {
            docs![global_id.to_debug_string()]
        }
        fn variant(&'a self, variant: &'b Variant) -> pretty::DocBuilder<'a, Self, A> {
            let payload = variant.arguments.iter().map(|(id, ty, attrs)| {
                docs![
                    self.attributes(attrs),
                    if variant.is_record {
                        docs![id, ":", space!()]
                    } else {
                        nil!()
                    },
                    ty
                ]
            });

            if variant.is_record {
                sep!("{", payload, "}")
            } else {
                sep!("(", payload, ")")
            }
        }
        fn item(&'a self, item: &'b Item) -> pretty::DocBuilder<'a, Self, A> {
            docs![&item.meta, item.kind()]
        }
        fn item_kind(&'a self, item_kind: &'b ItemKind) -> DocBuilder<'a, Self, A> {
            match item_kind {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    docs![
                        safety,
                        text!("fn"),
                        space!(),
                        name,
                        self.generic_params(&generics.params),
                        sep!("(", params, ")"),
                        self.where_clause(&generics.constraints),
                        docs![line_!(), body, line_!(),].nest(INDENT).braces()
                    ]
                }
                ItemKind::TyAlias {
                    name,
                    generics: _,
                    ty,
                } => docs!["type", space!(), name, space!(), "=", space!(), ty, ";"],
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => match &variants[..] {
                    [variant] if *is_struct => {
                        docs![
                            "struct",
                            space!(),
                            name,
                            self.generic_params(&generics.params),
                            variant,
                            if variant.is_record {
                                nil!()
                            } else {
                                docs![";"]
                            }
                        ]
                    }
                    _ => {
                        docs![
                            "enum",
                            space!(),
                            name,
                            self.generic_params(&generics.params),
                            sep!(
                                "{",
                                variants.iter().map(|variant| docs![
                                    &variant.name,
                                    space!(),
                                    variant
                                ]),
                                "}",
                            ),
                            self.where_clause(&generics.constraints),
                        ]
                    }
                },
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => docs![
                    "trait",
                    space!(),
                    name,
                    self.generic_params(&generics.params),
                    self.where_clause(&generics.constraints),
                    sep!("{", items, "}", nil!()),
                ],
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait: (trait_, trait_args),
                    items,
                    parent_bounds: _,
                    safety,
                } => docs![
                    safety,
                    "impl",
                    self.generic_params(&generics.params),
                    space!(),
                    trait_,
                    sep_opt!("<", trait_args, ">"),
                    space!(),
                    "for",
                    self_ty,
                    self.where_clause(&generics.constraints),
                    sep!("{", items, "}", nil!()),
                ],
                ItemKind::Alias { name, item } => todo!(),
                ItemKind::Use {
                    path,
                    is_external,
                    rename,
                } => todo!(),
                ItemKind::Quote { quote, origin } => todo!(),
                ItemKind::Error(error_node) => todo!(),
                ItemKind::Resugared(resugared_item_kind) => todo!(),
                ItemKind::NotImplementedYet => todo!(),
            }
        }
        fn impl_item(&'a self, impl_item: &'b ImplItem) -> pretty::DocBuilder<'a, Self, A> {
            match &impl_item.kind {
                ImplItemKind::Type { ty, parent_bounds } => todo!(),
                ImplItemKind::Fn { body, params } => docs![
                    &impl_item.meta,
                    text!("fn"),
                    space!(),
                    &impl_item.ident,
                    self.generic_params(&impl_item.generics.params),
                    sep!("(", params, ")"),
                    self.where_clause(&impl_item.generics.constraints),
                    docs![line_!(), body, line_!(),].nest(INDENT).braces()
                ],
                ImplItemKind::Resugared(resugared_impl_item_kind) => todo!(),
            }
        }
        fn metadata(&'a self, metadata: &'b Metadata) -> pretty::DocBuilder<'a, Self, A> {
            self.attributes(&metadata.attributes)
        }
        fn attribute(&'a self, attribute: &'b Attribute) -> pretty::DocBuilder<'a, Self, A> {
            match &attribute.kind {
                AttributeKind::Tool { path, tokens } => {
                    // docs!["#", "[", path.clone(), "(", tokens.clone(), ")", "]"]
                    nil!()
                }
                AttributeKind::DocComment { kind, body } => match kind {
                    DocCommentKind::Line => {
                        concat!(body.lines().map(|line| docs![format!("/// {line}")]))
                    }
                    DocCommentKind::Block => todo!(),
                },
            }
        }
    }
};
