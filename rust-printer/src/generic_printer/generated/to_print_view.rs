impl<'a> ToPrintView<'a> for origin::GenericValue {
    type Out = destination::GenericValue<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericValue::Ty(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericValue::Ty), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericValue::Ty(anon_field_0)
            }
            origin::GenericValue::Expr(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericValue::Expr), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericValue::Expr(anon_field_0)
            }
            origin::GenericValue::Lifetime => destination::GenericValue::Lifetime,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::PrimitiveTy {
    type Out = destination::PrimitiveTy<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::PrimitiveTy::Bool => destination::PrimitiveTy::Bool,
            origin::PrimitiveTy::Int(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PrimitiveTy::Int), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PrimitiveTy::Int(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Ty {
    type Out = destination::Ty<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Ty::Primitive(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Primitive), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Primitive(anon_field_0)
            }
            origin::Ty::Tuple(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Tuple), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Tuple(anon_field_0)
            }
            origin::Ty::App { head, args } => {
                let head = {
                    let context = PrintContext {
                        value: head,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::App), "::", stringify!(head)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let args = {
                    let context = PrintContext {
                        value: args,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::App), "::", stringify!(args)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::App { head, args }
            }
            origin::Ty::Arrow { inputs, output } => {
                let inputs = {
                    let context = PrintContext {
                        value: inputs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Arrow), "::", stringify!(inputs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let output = {
                    let context = PrintContext {
                        value: output,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Arrow), "::", stringify!(output)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Arrow {
                    inputs,
                    output,
                }
            }
            origin::Ty::Ref { inner, mutable } => {
                let inner = {
                    let context = PrintContext {
                        value: inner,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Ref), "::", stringify!(inner)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let mutable = {
                    let context = PrintContext {
                        value: mutable,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Ref), "::", stringify!(mutable)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Ref {
                    inner,
                    mutable,
                }
            }
            origin::Ty::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Error), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Error(anon_field_0)
            }
            origin::Ty::Param(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Param), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Param(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Metadata {
    type Out = destination::Metadata<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Metadata { span, attrs } => {
                let span = {
                    let context = PrintContext {
                        value: span,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Metadata), "::", stringify!(span)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let attrs = {
                    let context = PrintContext {
                        value: attrs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Metadata), "::", stringify!(attrs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Metadata {
                    span,
                    attrs,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Expr {
    type Out = destination::Expr<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Expr { kind, ty, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(meta))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Expr {
                    kind,
                    ty,
                    meta,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Pat {
    type Out = destination::Pat<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Pat { kind, ty, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(meta))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Pat { kind, ty, meta }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Arm {
    type Out = destination::Arm<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Arm { pat, body, guard, meta } => {
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(pat))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(body))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let guard = {
                    let context = PrintContext {
                        value: guard,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(guard))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(meta))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Arm {
                    pat,
                    body,
                    guard,
                    meta,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Guard {
    type Out = destination::Guard<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Guard { kind, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Guard), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Guard), "::", stringify!(meta))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Guard { kind, meta }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::BorrowKind {
    type Out = destination::BorrowKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::BorrowKind::Shared => destination::BorrowKind::Shared,
            origin::BorrowKind::Unique => destination::BorrowKind::Unique,
            origin::BorrowKind::Mut => destination::BorrowKind::Mut,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::BindingMode {
    type Out = destination::BindingMode<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::BindingMode::ByValue => destination::BindingMode::ByValue,
            origin::BindingMode::ByRef(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(BindingMode::ByRef), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::BindingMode::ByRef(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::PatKind {
    type Out = destination::PatKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::PatKind::Wild => destination::PatKind::Wild,
            origin::PatKind::Binding { mutable, var, mode } => {
                let mutable = {
                    let context = PrintContext {
                        value: mutable,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Binding), "::", stringify!(mutable)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let var = {
                    let context = PrintContext {
                        value: var,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Binding), "::", stringify!(var)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let mode = {
                    let context = PrintContext {
                        value: mode,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Binding), "::", stringify!(mode)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Binding {
                    mutable,
                    var,
                    mode,
                }
            }
            origin::PatKind::Construct { constructor, is_record, is_struct, fields } => {
                let constructor = {
                    let context = PrintContext {
                        value: constructor,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Construct), "::",
                                stringify!(constructor)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let is_record = {
                    let context = PrintContext {
                        value: is_record,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Construct), "::", stringify!(is_record)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let is_struct = {
                    let context = PrintContext {
                        value: is_struct,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Construct), "::", stringify!(is_struct)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let fields = {
                    let context = PrintContext {
                        value: fields,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Construct), "::", stringify!(fields)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                }
            }
            origin::PatKind::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Error), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Error(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GuardKind {
    type Out = destination::GuardKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GuardKind::IfLet { lhs, rhs } => {
                let lhs = {
                    let context = PrintContext {
                        value: lhs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GuardKind::IfLet), "::", stringify!(lhs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let rhs = {
                    let context = PrintContext {
                        value: rhs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GuardKind::IfLet), "::", stringify!(rhs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GuardKind::IfLet {
                    lhs,
                    rhs,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplExpr {
    type Out = destination::ImplExpr;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplExpr => destination::ImplExpr,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ExprKind {
    type Out = destination::ExprKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ExprKind::If { condition, then, else_ } => {
                let condition = {
                    let context = PrintContext {
                        value: condition,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::If), "::", stringify!(condition)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let then = {
                    let context = PrintContext {
                        value: then,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::If), "::", stringify!(then)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let else_ = {
                    let context = PrintContext {
                        value: else_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::If), "::", stringify!(else_)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::If {
                    condition,
                    then,
                    else_,
                }
            }
            origin::ExprKind::App { head, args, generic_args, bounds_impls, trait_ } => {
                let head = {
                    let context = PrintContext {
                        value: head,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::App), "::", stringify!(head)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let args = {
                    let context = PrintContext {
                        value: args,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::App), "::", stringify!(args)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let generic_args = {
                    let context = PrintContext {
                        value: generic_args,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::App), "::", stringify!(generic_args)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let bounds_impls = {
                    let context = PrintContext {
                        value: bounds_impls,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::App), "::", stringify!(bounds_impls)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let trait_ = {
                    let context = PrintContext {
                        value: trait_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::App), "::", stringify!(trait_)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                }
            }
            origin::ExprKind::Literal(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Literal), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Literal(anon_field_0)
            }
            origin::ExprKind::Array(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Array), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Array(anon_field_0)
            }
            origin::ExprKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
                base,
            } => {
                let constructor = {
                    let context = PrintContext {
                        value: constructor,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Construct), "::",
                                stringify!(constructor)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let is_record = {
                    let context = PrintContext {
                        value: is_record,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Construct), "::", stringify!(is_record)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let is_struct = {
                    let context = PrintContext {
                        value: is_struct,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Construct), "::", stringify!(is_struct)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let fields = {
                    let context = PrintContext {
                        value: fields,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Construct), "::", stringify!(fields)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let base = {
                    let context = PrintContext {
                        value: base,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Construct), "::", stringify!(base)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                }
            }
            origin::ExprKind::Match { scrutinee, arms } => {
                let scrutinee = {
                    let context = PrintContext {
                        value: scrutinee,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Match), "::", stringify!(scrutinee)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let arms = {
                    let context = PrintContext {
                        value: arms,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Match), "::", stringify!(arms)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Match {
                    scrutinee,
                    arms,
                }
            }
            origin::ExprKind::Tuple(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Tuple), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Tuple(anon_field_0)
            }
            origin::ExprKind::Borrow { mutable, inner } => {
                let mutable = {
                    let context = PrintContext {
                        value: mutable,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Borrow), "::", stringify!(mutable)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let inner = {
                    let context = PrintContext {
                        value: inner,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Borrow), "::", stringify!(inner)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Borrow {
                    mutable,
                    inner,
                }
            }
            origin::ExprKind::Deref(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Deref), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Deref(anon_field_0)
            }
            origin::ExprKind::Let { lhs, rhs, body } => {
                let lhs = {
                    let context = PrintContext {
                        value: lhs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Let), "::", stringify!(lhs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let rhs = {
                    let context = PrintContext {
                        value: rhs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Let), "::", stringify!(rhs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Let), "::", stringify!(body)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Let {
                    lhs,
                    rhs,
                    body,
                }
            }
            origin::ExprKind::GlobalId(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::GlobalId), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::GlobalId(anon_field_0)
            }
            origin::ExprKind::LocalId(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::LocalId), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::LocalId(anon_field_0)
            }
            origin::ExprKind::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Error), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Error(anon_field_0)
            }
            origin::ExprKind::Ascription { e, ty } => {
                let e = {
                    let context = PrintContext {
                        value: e,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Ascription), "::", stringify!(e)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Ascription), "::", stringify!(ty)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Ascription {
                    e,
                    ty,
                }
            }
            origin::ExprKind::Assign { lhs, value } => {
                let lhs = {
                    let context = PrintContext {
                        value: lhs,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Assign), "::", stringify!(lhs)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let value = {
                    let context = PrintContext {
                        value: value,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Assign), "::", stringify!(value)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Assign {
                    lhs,
                    value,
                }
            }
            origin::ExprKind::Loop { body, label } => {
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Loop), "::", stringify!(body)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let label = {
                    let context = PrintContext {
                        value: label,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Loop), "::", stringify!(label)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Loop {
                    body,
                    label,
                }
            }
            origin::ExprKind::Break { value, label } => {
                let value = {
                    let context = PrintContext {
                        value: value,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Break), "::", stringify!(value)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let label = {
                    let context = PrintContext {
                        value: label,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Break), "::", stringify!(label)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Break {
                    value,
                    label,
                }
            }
            origin::ExprKind::Return { value } => {
                let value = {
                    let context = PrintContext {
                        value: value,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Return), "::", stringify!(value)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Return {
                    value,
                }
            }
            origin::ExprKind::Continue { label } => {
                let label = {
                    let context = PrintContext {
                        value: label,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Continue), "::", stringify!(label)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Continue {
                    label,
                }
            }
            origin::ExprKind::Closure { params, body, captures } => {
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Closure), "::", stringify!(params)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Closure), "::", stringify!(body)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let captures = {
                    let context = PrintContext {
                        value: captures,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Closure), "::", stringify!(captures)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Closure {
                    params,
                    body,
                    captures,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GenericParamKind {
    type Out = destination::GenericParamKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericParamKind::Lifetime => destination::GenericParamKind::Lifetime,
            origin::GenericParamKind::Type => destination::GenericParamKind::Type,
            origin::GenericParamKind::Const { ty } => {
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericParamKind::Const), "::", stringify!(ty)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericParamKind::Const {
                    ty,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::TraitGoal {
    type Out = destination::TraitGoal<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::TraitGoal { trait_, args } => {
                let trait_ = {
                    let context = PrintContext {
                        value: trait_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(TraitGoal), "::", stringify!(trait_)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let args = {
                    let context = PrintContext {
                        value: args,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(TraitGoal), "::", stringify!(args)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitGoal {
                    trait_,
                    args,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplIdent {
    type Out = destination::ImplIdent<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplIdent { goal, name } => {
                let goal = {
                    let context = PrintContext {
                        value: goal,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplIdent), "::", stringify!(goal)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplIdent), "::", stringify!(name)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplIdent {
                    goal,
                    name,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ProjectionPredicate {
    type Out = destination::ProjectionPredicate;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ProjectionPredicate => destination::ProjectionPredicate,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GenericConstraint {
    type Out = destination::GenericConstraint<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericConstraint::Lifetime(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericConstraint::Lifetime), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericConstraint::Lifetime(anon_field_0)
            }
            origin::GenericConstraint::Type(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericConstraint::Type), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericConstraint::Type(anon_field_0)
            }
            origin::GenericConstraint::Projection(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericConstraint::Projection), "::",
                                stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericConstraint::Projection(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GenericParam {
    type Out = destination::GenericParam<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericParam { ident, meta, kind } => {
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericParam), "::", stringify!(ident)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericParam), "::", stringify!(meta)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericParam), "::", stringify!(kind)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericParam {
                    ident,
                    meta,
                    kind,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Generics {
    type Out = destination::Generics<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Generics { params, constraints } => {
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Generics), "::", stringify!(params)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let constraints = {
                    let context = PrintContext {
                        value: constraints,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Generics), "::", stringify!(constraints)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Generics {
                    params,
                    constraints,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::SafetyKind {
    type Out = destination::SafetyKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::SafetyKind::Safe => destination::SafetyKind::Safe,
            origin::SafetyKind::Unsafe => destination::SafetyKind::Unsafe,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Attribute {
    type Out = destination::Attribute;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Attribute => destination::Attribute,
        }
    }
}
/// A list of attributes.
pub type Attributes = Vec<Attribute>;
impl<'a> ToPrintView<'a> for origin::SpannedTy {
    type Out = destination::SpannedTy<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::SpannedTy { span, ty } => {
                let span = {
                    let context = PrintContext {
                        value: span,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(SpannedTy), "::", stringify!(span)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(SpannedTy), "::", stringify!(ty)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::SpannedTy { span, ty }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Param {
    type Out = destination::Param<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Param { pat, ty, attributes } => {
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Param), "::", stringify!(pat))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Param), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let attributes = {
                    let context = PrintContext {
                        value: attributes,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Param), "::", stringify!(attributes)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Param {
                    pat,
                    ty,
                    attributes,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ItemKind {
    type Out = destination::ItemKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ItemKind::Fn { name, generics, body, params, safety } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Fn), "::", stringify!(name)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let generics = {
                    let context = PrintContext {
                        value: generics,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Fn), "::", stringify!(generics)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Fn), "::", stringify!(body)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Fn), "::", stringify!(params)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let safety = {
                    let context = PrintContext {
                        value: safety,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Fn), "::", stringify!(safety)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                }
            }
            origin::ItemKind::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Error), "::", stringify!(anon_field_0)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Error(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Item {
    type Out = destination::Item<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Item { ident, kind, meta } => {
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(ident))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(meta))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Item {
                    ident,
                    kind,
                    meta,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ResugaredExprKind {
    type Out = destination::ResugaredExprKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ResugaredExprKind::ConstantApp { constant, generics } => {
                let constant = {
                    let context = PrintContext {
                        value: constant,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ResugaredExprKind::ConstantApp), "::",
                                stringify!(constant)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let generics = {
                    let context = PrintContext {
                        value: generics,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ResugaredExprKind::ConstantApp), "::",
                                stringify!(generics)
                            )
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ResugaredExprKind::ConstantApp {
                    constant,
                    generics,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ResugaredPatKind {
    type Out = destination::ResugaredPatKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            _ => {
                unreachable!(
                    "no variant, but references are always inhabited (see https://github.com/rust-lang/rust/issues/78123)"
                )
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ResugaredTy {
    type Out = destination::ResugaredTy;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)]
        parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            _ => {
                unreachable!(
                    "no variant, but references are always inhabited (see https://github.com/rust-lang/rust/issues/78123)"
                )
            }
        }
    }
}
