//! A Rust backend (and printer) for hax.

use super::prelude::*;
use crate::ast::identifiers::global_id::view::{PathSegment, View};
use std::cell::RefCell;

mod renamings;

/// The Rust printer.
#[derive(Default, Clone)]
pub struct RustPrinter {
    current_namespace: RefCell<Option<Vec<String>>>,
}
impl_doc_allocator_for!(RustPrinter);

impl Printer for RustPrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![
            Box::new(crate::resugarings::FunctionsToConstants),
            Box::new(crate::resugarings::Tuples),
        ]
    }

    const NAME: &str = "Rust";
}

impl RenderView for RustPrinter {
    fn render_path_segment(&self, seg: &PathSegment) -> Vec<String> {
        if let AnyKind::Constructor(constructor_kind) = seg.kind() {
            match constructor_kind {
                global_id::view::ConstructorKind::Constructor { ty } => {
                    if let global_id::view::TypeDefKind::Struct = ty.kind() {
                        return vec![
                            self.render_path_segment_payload(ty.lift().payload())
                                .to_string(),
                        ];
                    }
                }
            }
        };
        default::render_path_segment(self, seg)
    }
    fn render(&self, view: &View) -> Rendered {
        let (module_path, relative_path) = view.split_at_module();
        let path_segment = |seg| self.render_path_segment(seg);
        let mut rendered = Rendered {
            module: module_path.iter().flat_map(path_segment).collect(),
            path: relative_path.iter().flat_map(path_segment).collect(),
        };
        renamings::rename_rendered(&mut rendered);
        rendered
    }
}

/// The Rust backend.
pub struct RustBackend;

impl Backend for RustBackend {
    type Printer = RustPrinter;

    fn module_path(&self, module: &Module) -> camino::Utf8PathBuf {
        let printer = self.printer();
        let path = <RustPrinter as RenderView>::module(&printer, &module.ident.view());
        camino::Utf8PathBuf::from_iter(path).with_extension("rs")
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

    macro_rules! print_tuple {
        ($into_docs:ident) => {{
            let mut docs: Vec<_> = $into_docs.iter().map(|typ| docs![typ]).collect();
            if docs.len() == 1 {
                docs.push(nil![])
            }
            sep!("(", docs, ")")
        }};
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

    macro_rules! block {
        ($body:expr) => {
            docs![line!(), $body, line!()].group().nest(INDENT).braces()
        };
    }

    impl<'a, 'b> RustPrinter {
        fn generic_params<A: Clone + 'a>(
            &'a self,
            generic_params: &'b [GenericParam],
        ) -> DocBuilder<'a, Self, A> {
            let generic_params = generic_params
                .iter()
                .filter(|p| !matches!(&p.kind, GenericParamKind::Lifetime if p.ident.0.to_string() == "_"))
                .collect::<Vec<_>>();
            sep_opt!("<", generic_params, ">")
        }
        fn where_clause<A: Clone + 'a>(
            &'a self,
            constraints: &'b [GenericConstraint],
        ) -> DocBuilder<'a, Self, A> {
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
        fn attributes<A: Clone + 'a>(&'a self, attrs: &'b [Attribute]) -> DocBuilder<'a, Self, A> {
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

        fn id_name<A: Clone + 'a>(&'a self, id: GlobalId) -> DocBuilder<'a, Self, A> {
            let view = id.view();
            let path = <RustPrinter as RenderView>::render_strings(self, &view);
            let name = path.last().unwrap().clone();
            docs![if name == "_" {
                "___empty_name".into()
            } else {
                name
            }]
        }
    }

    impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for RustPrinter {
        const NAME: &'static str = "Rust";

        fn module(&'a self, module: &'b Module) -> DocBuilder<'a, Self, A> {
            let previous = self.current_namespace.borrow().clone();
            let view = module.ident.view();
            let module_path = <Self as RenderView>::module(self, &view);
            *self.current_namespace.borrow_mut() = Some(module_path);
            let doc = intersperse!(&module.items, docs![hardline!(), hardline!()]);
            *self.current_namespace.borrow_mut() = previous;
            doc
        }

        fn safety_kind(&'a self, safety_kind: &'b SafetyKind) -> DocBuilder<'a, Self, A> {
            match safety_kind {
                SafetyKind::Safe => nil!(),
                SafetyKind::Unsafe => docs![text!("unsafe"), space!()],
            }
        }
        fn param(&'a self, param: &'b Param) -> DocBuilder<'a, Self, A> {
            docs![&param.pat, ":", space!(), &param.ty]
        }
        fn binding_mode(&'a self, binding_mode: &'b BindingMode) -> DocBuilder<'a, Self, A> {
            match binding_mode {
                BindingMode::ByRef(BorrowKind::Mut) => docs!["ref mut", space!()],
                BindingMode::ByRef(_) => docs!["ref", space!()],
                _ => nil!(),
            }
        }
        fn pat(&'a self, pat: &'b Pat) -> DocBuilder<'a, Self, A> {
            match &*pat.kind {
                PatKind::Wild => docs!["_"],
                PatKind::Ascription { pat, ty } => docs![pat, ":", space!(), ty],
                PatKind::Or { sub_pats } => {
                    intersperse!(sub_pats, docs![line!(), "|", line!()])
                }
                PatKind::Array { args } => sep!("[", args, "]", "|"),
                PatKind::Deref { sub_pat } => docs!["&", sub_pat],
                PatKind::Constant { lit } => docs![lit],
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
                PatKind::Construct { .. } => todo!("resugaring"),
                PatKind::Resugared(resugared_pat_kind) => docs![resugared_pat_kind],
                PatKind::Error(_) => todo!("resugaring"),
            }
        }
        fn primitive_ty(&'a self, primitive_ty: &'b PrimitiveTy) -> DocBuilder<'a, Self, A> {
            match primitive_ty {
                PrimitiveTy::Bool => docs!["bool"],
                PrimitiveTy::Int(int_kind) => docs![int_kind],
                PrimitiveTy::Float(float_kind) => docs![float_kind],
                PrimitiveTy::Char => docs!["char"],
                PrimitiveTy::Str => docs!["str"],
            }
        }
        fn signedness(&'a self, signedness: &'b Signedness) -> DocBuilder<'a, Self, A> {
            match signedness {
                Signedness::Signed => docs!["i"],
                Signedness::Unsigned => docs!["u"],
            }
        }
        fn int_size(&'a self, int_size: &'b IntSize) -> DocBuilder<'a, Self, A> {
            docs![match int_size {
                IntSize::S8 => "8",
                IntSize::S16 => "16",
                IntSize::S32 => "32",
                IntSize::S64 => "64",
                IntSize::S128 => "128",
                IntSize::SSize => "size",
            }]
        }
        fn generic_param(&'a self, generic_param: &'b GenericParam) -> DocBuilder<'a, Self, A> {
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
        ) -> DocBuilder<'a, Self, A> {
            match generic_constraint {
                GenericConstraint::Lifetime(s) => docs![s.clone()],
                GenericConstraint::Type(impl_ident) => docs![impl_ident],
                GenericConstraint::Projection(projection_predicate) => docs![projection_predicate],
            }
        }
        fn impl_ident(&'a self, impl_ident: &'b ImplIdent) -> DocBuilder<'a, Self, A> {
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

        fn ty(&'a self, ty: &'b Ty) -> DocBuilder<'a, Self, A> {
            match ty.kind() {
                TyKind::Primitive(primitive_ty) => docs![primitive_ty],
                // TyKind::Tuple(items) => intersperse!(items, docs![",", line!()])
                //     .nest(INDENT)
                //     .group(),
                TyKind::App { head, args } => docs![head, sep_opt!("<", args, ">")],
                TyKind::Arrow { inputs, output } => {
                    docs!["fn", sep!("(", inputs, ")"), reflow!(" -> "), output]
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region: _,
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
                TyKind::Slice(ty) => docs![ty].brackets(),
                TyKind::Array { ty, length } => {
                    docs![ty, ";", space!(), length.as_ref()].brackets()
                }
                TyKind::RawPointer => todo!(),
                TyKind::AssociatedType { impl_, item } => docs![impl_, "::", item],
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
                TyKind::Resugared(resugared_ty_kind) => docs![resugared_ty_kind],
                TyKind::Error(_) => todo!("resugaring"),
            }
        }
        fn resugared_ty_kind(
            &'a self,
            resugared_ty_kind: &'b ResugaredTyKind,
        ) -> DocBuilder<'a, Self, A> {
            match resugared_ty_kind {
                ResugaredTyKind::Tuple(types) => print_tuple!(types),
            }
        }
        fn literal(&'a self, literal: &'b Literal) -> DocBuilder<'a, Self, A> {
            match literal {
                Literal::String(symbol) => docs![symbol],
                Literal::Char(ch) => text!(format!("{}", ch)),
                Literal::Bool(b) => text!(format!("{}", b)),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => docs![if *negative { docs!["-"] } else { nil!() }, value, kind],
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => docs![if *negative { docs!["-"] } else { nil!() }, value, kind],
            }
        }
        fn int_kind(&'a self, int_kind: &'b IntKind) -> DocBuilder<'a, Self, A> {
            docs![&int_kind.signedness, &int_kind.size]
        }
        fn trait_goal(&'a self, trait_goal: &'b TraitGoal) -> DocBuilder<'a, Self, A> {
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
        fn generic_value(&'a self, generic_value: &'b GenericValue) -> DocBuilder<'a, Self, A> {
            match generic_value {
                GenericValue::Ty(ty) => docs![ty],
                GenericValue::Expr(expr) => docs![expr],
                GenericValue::Lifetime => docs!["'_"],
            }
        }
        fn arm(&'a self, arm: &'b Arm) -> DocBuilder<'a, Self, A> {
            docs![
                &arm.pat,
                arm.guard.as_ref().map(|guard| docs!["if", space!(), guard]),
                reflow!(" => "),
                block![&arm.body],
            ]
        }
        fn expr(&'a self, expr: &'b Expr) -> DocBuilder<'a, Self, A> {
            match &*expr.kind {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => docs![
                    "if",
                    space!(),
                    docs![condition].parens(),
                    space!(),
                    block![then],
                    else_
                        .as_ref()
                        .map(|doc| docs![reflow!(" else "), block![doc]])
                        .unwrap_or(nil!())
                ],
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls: _, // this is implicit in Rust
                    trait_,
                } => {
                    mod names {
                        pub use crate::names::rust_primitives::hax::{
                            cast_op, deref_op, logical_op_and, logical_op_or,
                        };
                    }
                    use ExprKind::GlobalId;
                    match (&*head.kind, &args[..]) {
                        (GlobalId(names::deref_op), [reference]) => {
                            Some(docs!["*", docs![reference].parens()])
                        }
                        (GlobalId(names::cast_op), [value]) => {
                            Some(docs![docs![value].parens(), reflow!(" as "), &expr.ty])
                        }
                        (GlobalId(names::logical_op_and), [lhs, rhs]) => Some(docs![
                            docs![lhs].parens(),
                            reflow!(" && "),
                            docs![rhs].parens()
                        ]),
                        (GlobalId(names::logical_op_or), [lhs, rhs]) => Some(docs![
                            docs![lhs].parens(),
                            reflow!(" || "),
                            docs![rhs].parens()
                        ]),
                        _ => None,
                    }
                    .unwrap_or_else(|| match (trait_, &*head.kind) {
                        (Some((trait_impl_expr, _trait_args)), GlobalId(head)) => {
                            docs![
                                &trait_impl_expr.goal,
                                "::",
                                self.id_name(*head),
                                sep_opt!("::<", generic_args, ">"),
                                sep!("(", args, ")")
                            ]
                        }
                        _ => docs![
                            head,
                            sep_opt!("::<", generic_args, ">"),
                            sep!("(", args, ")")
                        ],
                    })
                }
                ExprKind::Literal(literal) => docs![literal],
                ExprKind::Array(exprs) => sep!("[", exprs, "]"),
                ExprKind::Construct {
                    constructor,
                    is_record,
                    fields,
                    // TODO: complete constructors with base
                    ..
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
                    docs![
                        "match",
                        space!(),
                        scrutinee,
                        space!(),
                        block!(intersperse!(arms, hardline!())),
                    ]
                }
                ExprKind::Borrow { mutable, inner } => {
                    docs!["&", if *mutable { reflow!["mut "] } else { nil!() }, inner]
                }
                ExprKind::AddressOf { mutable, inner } => docs![
                    inner,
                    reflow!(" as *"),
                    if *mutable { reflow!["mut "] } else { nil!() },
                    docs![&expr.ty]
                ]
                .parens(),
                ExprKind::Deref(expr) => docs!["*", expr],
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
                    state: None,
                    control_flow: None,
                    label: None,
                } => match &**kind {
                    LoopKind::UnconditionalLoop => docs!["loop", space!(), block![body]],
                    LoopKind::WhileLoop { condition } => {
                        docs!["while", space!(), condition, space!(), block![body]]
                    }
                    LoopKind::ForLoop { pat, iterator } => {
                        docs![
                            "for",
                            space!(),
                            pat,
                            reflow!(" in "),
                            iterator,
                            space!(),
                            block![body]
                        ]
                    }
                    LoopKind::ForIndexLoop {
                        start,
                        end,
                        var,
                        var_ty: _,
                    } => docs![
                        "for",
                        space!(),
                        var,
                        reflow!(" in "),
                        start,
                        "..",
                        end,
                        space!(),
                        block![body]
                    ],
                },
                ExprKind::Loop { .. } => {
                    todo!("loop with explicit state or with a label")
                }
                ExprKind::Break { value, label: None } => docs!["break", space!(), value],
                ExprKind::Break { .. } => todo!("break with a label"),
                ExprKind::Return { value } => docs!["return", space!(), value],
                ExprKind::Continue { label: None } => docs!["continue"],
                ExprKind::Continue { .. } => todo!("continue with a label"),
                ExprKind::Closure {
                    params,
                    body,
                    captures: _,
                } => docs![
                    intersperse!(params, docs![",", space!()]).enclose("|", "|"),
                    body
                ],
                ExprKind::Block { body, safety_mode } => {
                    docs![safety_mode, block![body]]
                }
                ExprKind::Quote { contents } => docs![contents],
                ExprKind::Resugared(resugared_expr_kind) => docs![resugared_expr_kind],
                ExprKind::Error { .. } => todo!("resugaring"),
            }
        }
        fn resugared_expr_kind(
            &'a self,
            resugared_expr_kind: &'b ResugaredExprKind,
        ) -> DocBuilder<'a, Self, A> {
            match resugared_expr_kind {
                ResugaredExprKind::BinOp { .. } => unreachable!("BinOp resugaring not active"),
                ResugaredExprKind::Tuple(values) => print_tuple!(values),
            }
        }

        fn lhs(&'a self, lhs: &'b Lhs) -> DocBuilder<'a, Self, A> {
            match lhs {
                Lhs::LocalVar { var, ty: _ } => docs![var],
                Lhs::ArbitraryExpr(expr) => docs![std::ops::Deref::deref(expr)],
                Lhs::FieldAccessor { e, ty: _, field } => {
                    docs![std::ops::Deref::deref(e), ".", field]
                }
                Lhs::ArrayAccessor { e, ty: _, index } => {
                    docs![std::ops::Deref::deref(e), docs!(index).brackets()]
                }
            }
        }
        fn global_id(&'a self, global_id: &'b GlobalId) -> DocBuilder<'a, Self, A> {
            let view = global_id.view();
            let module = <Self as RenderView>::module(self, &view);
            if Some(module) == *self.current_namespace.borrow() {
                let rendered = self.render(&view);
                docs![rendered.path.join("::")]
            } else {
                docs![self.render_string(&view)]
            }
        }
        fn variant(&'a self, variant: &'b Variant) -> DocBuilder<'a, Self, A> {
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
        fn item(&'a self, item: &'b Item) -> DocBuilder<'a, Self, A> {
            docs![&item.meta, item.kind()]
        }
        fn resugared_item_kind(
            &'a self,
            resugared_item_kind: &'b ResugaredItemKind,
        ) -> DocBuilder<'a, Self, A> {
            match resugared_item_kind {
                ResugaredItemKind::Constant { name, body, .. } => {
                    docs![
                        "const",
                        space!(),
                        self.id_name(*name),
                        ":",
                        space!(),
                        &body.ty,
                        reflow!(" = "),
                        docs![body].braces(),
                        ";"
                    ]
                }
            }
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
                        self.id_name(*name),
                        self.generic_params(&generics.params),
                        sep!("(", params, ")"),
                        reflow!(" -> "),
                        &body.ty,
                        space!(),
                        self.where_clause(&generics.constraints),
                        block![body]
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
                            self.id_name(*name),
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
                            self.id_name(*name),
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
                    self.id_name(*name),
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
                    sep_opt!("<", trait_args[1..], ">"),
                    space!(),
                    "for",
                    space!(),
                    self_ty,
                    self.where_clause(&generics.constraints),
                    sep!("{", items, "}", nil!()),
                ],
                ItemKind::Alias { name, item } => {
                    docs!["type", self.id_name(*name), reflow!(" = "), item, ";"]
                }
                ItemKind::Use { .. } => nil!(),
                ItemKind::Quote { quote, .. } => docs![quote],
                ItemKind::Error { .. } => todo!("resugaring"),
                ItemKind::Resugared(resugared_item_kind) => docs![resugared_item_kind],
                ItemKind::NotImplementedYet => docs!["/* `NotImplementedYet` item */"],
            }
        }
        fn impl_item(&'a self, impl_item: &'b ImplItem) -> DocBuilder<'a, Self, A> {
            match &impl_item.kind {
                ImplItemKind::Type {
                    ty,
                    parent_bounds: _,
                } => docs![
                    &impl_item.meta,
                    reflow!("type "),
                    self.id_name(impl_item.ident),
                    reflow!(" = "),
                    ty,
                    ";"
                ],
                ImplItemKind::Fn { body, params } => docs![
                    &impl_item.meta,
                    text!("fn"),
                    space!(),
                    self.id_name(impl_item.ident),
                    self.generic_params(&impl_item.generics.params),
                    sep!("(", params, ")"),
                    reflow!(" -> "),
                    &body.ty,
                    space!(),
                    self.where_clause(&impl_item.generics.constraints),
                    docs![line_!(), body, line_!(),].nest(INDENT).braces()
                ],
                ImplItemKind::Resugared(_resugared_impl_item_kind) => todo!(),
            }
        }
        fn metadata(&'a self, metadata: &'b Metadata) -> DocBuilder<'a, Self, A> {
            self.attributes(&metadata.attributes)
        }
        fn attribute(&'a self, attribute: &'b Attribute) -> DocBuilder<'a, Self, A> {
            match &attribute.kind {
                AttributeKind::Tool { .. } => nil!(),
                AttributeKind::DocComment { kind, body } => match kind {
                    DocCommentKind::Line => {
                        intersperse!(
                            body.lines().map(|line| docs![format!("/// {line}")]),
                            hardline!()
                        )
                    }
                    DocCommentKind::Block => {
                        docs![
                            "/**",
                            intersperse!(body.lines().map(|line| line.to_string()), hardline!()),
                            "*/"
                        ]
                    }
                },
            }
        }
    }
};
