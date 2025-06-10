impl<'a> ToPrintView<'a> for origin::GenericValue {
    type Out = destination::GenericValue<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericValue::Ty(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericValue::Ty),
                                "::",
                                stringify!(anon_field_0)
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
                                stringify!(GenericValue::Expr),
                                "::",
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::PrimitiveTy::Bool => destination::PrimitiveTy::Bool,
            origin::PrimitiveTy::Int(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PrimitiveTy::Int),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PrimitiveTy::Int(anon_field_0)
            }
            origin::PrimitiveTy::Float(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PrimitiveTy::Float),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PrimitiveTy::Float(anon_field_0)
            }
            origin::PrimitiveTy::Char => destination::PrimitiveTy::Char,
            origin::PrimitiveTy::Str => destination::PrimitiveTy::Str,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Region {
    type Out = destination::Region;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Region => destination::Region,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Ty {
    type Out = destination::Ty<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Ty::Primitive(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Primitive),
                                "::",
                                stringify!(anon_field_0)
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
                                stringify!(Ty::Tuple),
                                "::",
                                stringify!(anon_field_0)
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
                            position: concat!(stringify!(Ty::App), "::", stringify!(head)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let args = {
                    let context = PrintContext {
                        value: args,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::App), "::", stringify!(args)).into(),
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
                            position: concat!(stringify!(Ty::Arrow), "::", stringify!(inputs))
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
                            position: concat!(stringify!(Ty::Arrow), "::", stringify!(output))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Arrow { inputs, output }
            }
            origin::Ty::Ref {
                inner,
                mutable,
                region,
            } => {
                let inner = {
                    let context = PrintContext {
                        value: inner,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Ref), "::", stringify!(inner)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let mutable = {
                    let context = PrintContext {
                        value: mutable,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Ref), "::", stringify!(mutable))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let region = {
                    let context = PrintContext {
                        value: region,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Ref), "::", stringify!(region)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Ref {
                    inner,
                    mutable,
                    region,
                }
            }
            origin::Ty::Param(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Param),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Param(anon_field_0)
            }
            origin::Ty::Slice(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Slice),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Slice(anon_field_0)
            }
            origin::Ty::Array { ty, length } => {
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Array), "::", stringify!(ty)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let length = {
                    let context = PrintContext {
                        value: length,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Array), "::", stringify!(length))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Array { ty, length }
            }
            origin::Ty::RawPointer => destination::Ty::RawPointer,
            origin::Ty::AssociatedType { impl_, item } => {
                let impl_ = {
                    let context = PrintContext {
                        value: impl_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::AssociatedType),
                                "::",
                                stringify!(impl_)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let item = {
                    let context = PrintContext {
                        value: item,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::AssociatedType),
                                "::",
                                stringify!(item)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::AssociatedType { impl_, item }
            }
            origin::Ty::Opaque(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Opaque),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Opaque(anon_field_0)
            }
            origin::Ty::Dyn(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Ty::Dyn), "::", stringify!(anon_field_0))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Dyn(anon_field_0)
            }
            origin::Ty::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Ty::Error),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Ty::Error(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::DynTraitGoal {
    type Out = destination::DynTraitGoal<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                let trait_ = {
                    let context = PrintContext {
                        value: trait_,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(DynTraitGoal), "::", stringify!(trait_))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let non_self_args = {
                    let context = PrintContext {
                        value: non_self_args,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(DynTraitGoal),
                                "::",
                                stringify!(non_self_args)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::DynTraitGoal {
                    trait_,
                    non_self_args,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Metadata {
    type Out = destination::Metadata<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Metadata { span, attributes } => {
                let span = {
                    let context = PrintContext {
                        value: span,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Metadata), "::", stringify!(span)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let attributes = {
                    let context = PrintContext {
                        value: attributes,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Metadata), "::", stringify!(attributes))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Metadata { span, attributes }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Expr {
    type Out = destination::Expr<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Expr { kind, ty, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(ty)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Expr), "::", stringify!(meta)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Expr { kind, ty, meta }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Pat {
    type Out = destination::Pat<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Pat { kind, ty, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(ty)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Pat), "::", stringify!(meta)).into(),
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(pat)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(body)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let guard = {
                    let context = PrintContext {
                        value: guard,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(guard)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Arm), "::", stringify!(meta)).into(),
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Guard { kind, meta } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Guard), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Guard), "::", stringify!(meta)).into(),
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::BindingMode::ByValue => destination::BindingMode::ByValue,
            origin::BindingMode::ByRef(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(BindingMode::ByRef),
                                "::",
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::PatKind::Wild => destination::PatKind::Wild,
            origin::PatKind::Ascription { ty, typ_span, pat } => {
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Ascription),
                                "::",
                                stringify!(ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let typ_span = {
                    let context = PrintContext {
                        value: typ_span,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Ascription),
                                "::",
                                stringify!(typ_span)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Ascription),
                                "::",
                                stringify!(pat)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Ascription { ty, typ_span, pat }
            }
            origin::PatKind::Or { sub_pats } => {
                let sub_pats = {
                    let context = PrintContext {
                        value: sub_pats,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(PatKind::Or), "::", stringify!(sub_pats))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Or { sub_pats }
            }
            origin::PatKind::Array { args } => {
                let args = {
                    let context = PrintContext {
                        value: args,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(PatKind::Array), "::", stringify!(args))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Array { args }
            }
            origin::PatKind::Deref { sub_pat } => {
                let sub_pat = {
                    let context = PrintContext {
                        value: sub_pat,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Deref),
                                "::",
                                stringify!(sub_pat)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Deref { sub_pat }
            }
            origin::PatKind::Constant { lit } => {
                let lit = {
                    let context = PrintContext {
                        value: lit,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(PatKind::Constant), "::", stringify!(lit))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::PatKind::Constant { lit }
            }
            origin::PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                let mutable = {
                    let context = PrintContext {
                        value: mutable,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Binding),
                                "::",
                                stringify!(mutable)
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
                            position: concat!(stringify!(PatKind::Binding), "::", stringify!(var))
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
                            position: concat!(stringify!(PatKind::Binding), "::", stringify!(mode))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let sub_pat = {
                    let context = PrintContext {
                        value: sub_pat,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Binding),
                                "::",
                                stringify!(sub_pat)
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
                    sub_pat,
                }
            }
            origin::PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                let constructor = {
                    let context = PrintContext {
                        value: constructor,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(PatKind::Construct),
                                "::",
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
                                stringify!(PatKind::Construct),
                                "::",
                                stringify!(is_record)
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
                                stringify!(PatKind::Construct),
                                "::",
                                stringify!(is_struct)
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
                                stringify!(PatKind::Construct),
                                "::",
                                stringify!(fields)
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
                                stringify!(PatKind::Error),
                                "::",
                                stringify!(anon_field_0)
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GuardKind::IfLet { lhs, rhs } => {
                let lhs = {
                    let context = PrintContext {
                        value: lhs,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(GuardKind::IfLet), "::", stringify!(lhs))
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
                            position: concat!(stringify!(GuardKind::IfLet), "::", stringify!(rhs))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GuardKind::IfLet { lhs, rhs }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Lhs {
    type Out = destination::Lhs<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Lhs::LocalVar { var, ty } => {
                let var = {
                    let context = PrintContext {
                        value: var,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Lhs::LocalVar), "::", stringify!(var))
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
                            position: concat!(stringify!(Lhs::LocalVar), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Lhs::LocalVar { var, ty }
            }
            origin::Lhs::ArbitraryExpr(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Lhs::ArbitraryExpr),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Lhs::ArbitraryExpr(anon_field_0)
            }
            origin::Lhs::FieldAccessor { e, ty, field } => {
                let e = {
                    let context = PrintContext {
                        value: e,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Lhs::FieldAccessor), "::", stringify!(e))
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
                            position: concat!(stringify!(Lhs::FieldAccessor), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let field = {
                    let context = PrintContext {
                        value: field,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Lhs::FieldAccessor),
                                "::",
                                stringify!(field)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Lhs::FieldAccessor { e, ty, field }
            }
            origin::Lhs::ArrayAccessor { e, ty, index } => {
                let e = {
                    let context = PrintContext {
                        value: e,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Lhs::ArrayAccessor), "::", stringify!(e))
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
                            position: concat!(stringify!(Lhs::ArrayAccessor), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let index = {
                    let context = PrintContext {
                        value: index,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(Lhs::ArrayAccessor),
                                "::",
                                stringify!(index)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Lhs::ArrayAccessor { e, ty, index }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplExpr {
    type Out = destination::ImplExpr<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplExpr { kind, goal } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplExpr), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let goal = {
                    let context = PrintContext {
                        value: goal,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplExpr), "::", stringify!(goal)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExpr { kind, goal }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplExprKind {
    type Out = destination::ImplExprKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplExprKind::Self_ => destination::ImplExprKind::Self_,
            origin::ImplExprKind::Concrete(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Concrete),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::Concrete(anon_field_0)
            }
            origin::ImplExprKind::LocalBound { id } => {
                let id = {
                    let context = PrintContext {
                        value: id,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::LocalBound),
                                "::",
                                stringify!(id)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::LocalBound { id }
            }
            origin::ImplExprKind::Parent { impl_, ident } => {
                let impl_ = {
                    let context = PrintContext {
                        value: impl_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Parent),
                                "::",
                                stringify!(impl_)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Parent),
                                "::",
                                stringify!(ident)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::Parent { impl_, ident }
            }
            origin::ImplExprKind::Projection { impl_, item, ident } => {
                let impl_ = {
                    let context = PrintContext {
                        value: impl_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Projection),
                                "::",
                                stringify!(impl_)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let item = {
                    let context = PrintContext {
                        value: item,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Projection),
                                "::",
                                stringify!(item)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Projection),
                                "::",
                                stringify!(ident)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::Projection { impl_, item, ident }
            }
            origin::ImplExprKind::ImplApp { impl_, args } => {
                let impl_ = {
                    let context = PrintContext {
                        value: impl_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::ImplApp),
                                "::",
                                stringify!(impl_)
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
                                stringify!(ImplExprKind::ImplApp),
                                "::",
                                stringify!(args)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::ImplApp { impl_, args }
            }
            origin::ImplExprKind::Dyn => destination::ImplExprKind::Dyn,
            origin::ImplExprKind::Builtin(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplExprKind::Builtin),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplExprKind::Builtin(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplItem {
    type Out = destination::ImplItem<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplItem), "::", stringify!(meta)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let generics = {
                    let context = PrintContext {
                        value: generics,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplItem), "::", stringify!(generics))
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
                            position: concat!(stringify!(ImplItem), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplItem), "::", stringify!(ident)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplItem {
                    meta,
                    generics,
                    kind,
                    ident,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplItemKind {
    type Out = destination::ImplItemKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplItemKind::Type { ty, parent_bounds } => {
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplItemKind::Type), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let parent_bounds = {
                    let context = PrintContext {
                        value: parent_bounds,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ImplItemKind::Type),
                                "::",
                                stringify!(parent_bounds)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplItemKind::Type { ty, parent_bounds }
            }
            origin::ImplItemKind::Fn { body, params } => {
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplItemKind::Fn), "::", stringify!(body))
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
                                stringify!(ImplItemKind::Fn),
                                "::",
                                stringify!(params)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplItemKind::Fn { body, params }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::TraitItem {
    type Out = destination::TraitItem<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::TraitItem {
                kind,
                generics,
                ident,
                meta,
            } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(TraitItem), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let generics = {
                    let context = PrintContext {
                        value: generics,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(TraitItem), "::", stringify!(generics))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(TraitItem), "::", stringify!(ident))
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
                            position: concat!(stringify!(TraitItem), "::", stringify!(meta)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitItem {
                    kind,
                    generics,
                    ident,
                    meta,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::TraitItemKind {
    type Out = destination::TraitItemKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::TraitItemKind::Type(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(TraitItemKind::Type),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitItemKind::Type(anon_field_0)
            }
            origin::TraitItemKind::Fn(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(TraitItemKind::Fn),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitItemKind::Fn(anon_field_0)
            }
            origin::TraitItemKind::Default { params, body } => {
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(TraitItemKind::Default),
                                "::",
                                stringify!(params)
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
                                stringify!(TraitItemKind::Default),
                                "::",
                                stringify!(body)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitItemKind::Default { params, body }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::QuoteContent {
    type Out = destination::QuoteContent<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::QuoteContent::Verbatim(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(QuoteContent::Verbatim),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::QuoteContent::Verbatim(anon_field_0)
            }
            origin::QuoteContent::Expr(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(QuoteContent::Expr),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::QuoteContent::Expr(anon_field_0)
            }
            origin::QuoteContent::Pattern(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(QuoteContent::Pattern),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::QuoteContent::Pattern(anon_field_0)
            }
            origin::QuoteContent::Typ(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(QuoteContent::Typ),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::QuoteContent::Typ(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Quote {
    type Out = destination::Quote<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Quote(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Quote), "::", stringify!(anon_field_0))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Quote(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ItemQuoteOrigin {
    type Out = destination::ItemQuoteOrigin<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let item_kind = {
                    let context = PrintContext {
                        value: item_kind,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemQuoteOrigin),
                                "::",
                                stringify!(item_kind)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let item_ident = {
                    let context = PrintContext {
                        value: item_ident,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemQuoteOrigin),
                                "::",
                                stringify!(item_ident)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let position = {
                    let context = PrintContext {
                        value: position,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemQuoteOrigin),
                                "::",
                                stringify!(position)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ItemQuoteOriginKind {
    type Out = destination::ItemQuoteOriginKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ItemQuoteOriginKind::Fn => destination::ItemQuoteOriginKind::Fn,
            origin::ItemQuoteOriginKind::TyAlias => destination::ItemQuoteOriginKind::TyAlias,
            origin::ItemQuoteOriginKind::Type => destination::ItemQuoteOriginKind::Type,
            origin::ItemQuoteOriginKind::MacroInvocation => {
                destination::ItemQuoteOriginKind::MacroInvocation
            }
            origin::ItemQuoteOriginKind::Trait => destination::ItemQuoteOriginKind::Trait,
            origin::ItemQuoteOriginKind::Impl => destination::ItemQuoteOriginKind::Impl,
            origin::ItemQuoteOriginKind::Alias => destination::ItemQuoteOriginKind::Alias,
            origin::ItemQuoteOriginKind::Use => destination::ItemQuoteOriginKind::Use,
            origin::ItemQuoteOriginKind::Quote => destination::ItemQuoteOriginKind::Quote,
            origin::ItemQuoteOriginKind::HaxError => destination::ItemQuoteOriginKind::HaxError,
            origin::ItemQuoteOriginKind::NotImplementedYet => {
                destination::ItemQuoteOriginKind::NotImplementedYet
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ItemQuoteOriginPosition {
    type Out = destination::ItemQuoteOriginPosition;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ItemQuoteOriginPosition::Before => destination::ItemQuoteOriginPosition::Before,
            origin::ItemQuoteOriginPosition::After => destination::ItemQuoteOriginPosition::After,
            origin::ItemQuoteOriginPosition::Replace => {
                destination::ItemQuoteOriginPosition::Replace
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::LoopKind {
    type Out = destination::LoopKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::LoopKind::UnconditionalLoop => destination::LoopKind::UnconditionalLoop,
            origin::LoopKind::WhileLoop { condition } => {
                let condition = {
                    let context = PrintContext {
                        value: condition,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(LoopKind::WhileLoop),
                                "::",
                                stringify!(condition)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::LoopKind::WhileLoop { condition }
            }
            origin::LoopKind::ForLoop { pat, it } => {
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(LoopKind::ForLoop), "::", stringify!(pat))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let it = {
                    let context = PrintContext {
                        value: it,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(LoopKind::ForLoop), "::", stringify!(it))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::LoopKind::ForLoop { pat, it }
            }
            origin::LoopKind::ForIndexLoop {
                start,
                end,
                var,
                var_ty,
            } => {
                let start = {
                    let context = PrintContext {
                        value: start,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(LoopKind::ForIndexLoop),
                                "::",
                                stringify!(start)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let end = {
                    let context = PrintContext {
                        value: end,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(LoopKind::ForIndexLoop),
                                "::",
                                stringify!(end)
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
                                stringify!(LoopKind::ForIndexLoop),
                                "::",
                                stringify!(var)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let var_ty = {
                    let context = PrintContext {
                        value: var_ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(LoopKind::ForIndexLoop),
                                "::",
                                stringify!(var_ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ControlFlowKind {
    type Out = destination::ControlFlowKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ControlFlowKind::BreakOnly => destination::ControlFlowKind::BreakOnly,
            origin::ControlFlowKind::BreakOrReturn => destination::ControlFlowKind::BreakOrReturn,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::LoopState {
    type Out = destination::LoopState<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::LoopState { init, body_pat } => {
                let init = {
                    let context = PrintContext {
                        value: init,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(LoopState), "::", stringify!(init)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let body_pat = {
                    let context = PrintContext {
                        value: body_pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(LoopState), "::", stringify!(body_pat))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::LoopState { init, body_pat }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ExprKind {
    type Out = destination::ExprKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ExprKind::If {
                condition,
                then,
                else_,
            } => {
                let condition = {
                    let context = PrintContext {
                        value: condition,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::If),
                                "::",
                                stringify!(condition)
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
                            position: concat!(stringify!(ExprKind::If), "::", stringify!(then))
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
                            position: concat!(stringify!(ExprKind::If), "::", stringify!(else_))
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
            origin::ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let head = {
                    let context = PrintContext {
                        value: head,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::App), "::", stringify!(head))
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
                            position: concat!(stringify!(ExprKind::App), "::", stringify!(args))
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
                                stringify!(ExprKind::App),
                                "::",
                                stringify!(generic_args)
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
                                stringify!(ExprKind::App),
                                "::",
                                stringify!(bounds_impls)
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
                            position: concat!(stringify!(ExprKind::App), "::", stringify!(trait_))
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
                                stringify!(ExprKind::Literal),
                                "::",
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
                                stringify!(ExprKind::Array),
                                "::",
                                stringify!(anon_field_0)
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
                                stringify!(ExprKind::Construct),
                                "::",
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
                                stringify!(ExprKind::Construct),
                                "::",
                                stringify!(is_record)
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
                                stringify!(ExprKind::Construct),
                                "::",
                                stringify!(is_struct)
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
                                stringify!(ExprKind::Construct),
                                "::",
                                stringify!(fields)
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
                                stringify!(ExprKind::Construct),
                                "::",
                                stringify!(base)
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
                                stringify!(ExprKind::Match),
                                "::",
                                stringify!(scrutinee)
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
                            position: concat!(stringify!(ExprKind::Match), "::", stringify!(arms))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Match { scrutinee, arms }
            }
            origin::ExprKind::Tuple(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Tuple),
                                "::",
                                stringify!(anon_field_0)
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
                                stringify!(ExprKind::Borrow),
                                "::",
                                stringify!(mutable)
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
                                stringify!(ExprKind::Borrow),
                                "::",
                                stringify!(inner)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Borrow { mutable, inner }
            }
            origin::ExprKind::AddressOf { mutability, inner } => {
                let mutability = {
                    let context = PrintContext {
                        value: mutability,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::AddressOf),
                                "::",
                                stringify!(mutability)
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
                                stringify!(ExprKind::AddressOf),
                                "::",
                                stringify!(inner)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::AddressOf { mutability, inner }
            }
            origin::ExprKind::Deref(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Deref),
                                "::",
                                stringify!(anon_field_0)
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
                            position: concat!(stringify!(ExprKind::Let), "::", stringify!(lhs))
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
                            position: concat!(stringify!(ExprKind::Let), "::", stringify!(rhs))
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
                            position: concat!(stringify!(ExprKind::Let), "::", stringify!(body))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Let { lhs, rhs, body }
            }
            origin::ExprKind::GlobalId(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::GlobalId),
                                "::",
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
                                stringify!(ExprKind::LocalId),
                                "::",
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
            origin::ExprKind::Ascription { e, ty } => {
                let e = {
                    let context = PrintContext {
                        value: e,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Ascription),
                                "::",
                                stringify!(e)
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
                                stringify!(ExprKind::Ascription),
                                "::",
                                stringify!(ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Ascription { e, ty }
            }
            origin::ExprKind::Assign { lhs, value } => {
                let lhs = {
                    let context = PrintContext {
                        value: lhs,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::Assign), "::", stringify!(lhs))
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
                                stringify!(ExprKind::Assign),
                                "::",
                                stringify!(value)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Assign { lhs, value }
            }
            origin::ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::Loop), "::", stringify!(body))
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
                            position: concat!(stringify!(ExprKind::Loop), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let state = {
                    let context = PrintContext {
                        value: state,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::Loop), "::", stringify!(state))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let control_flow = {
                    let context = PrintContext {
                        value: control_flow,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Loop),
                                "::",
                                stringify!(control_flow)
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
                            position: concat!(stringify!(ExprKind::Loop), "::", stringify!(label))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                }
            }
            origin::ExprKind::Break { value, label } => {
                let value = {
                    let context = PrintContext {
                        value: value,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::Break), "::", stringify!(value))
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
                            position: concat!(stringify!(ExprKind::Break), "::", stringify!(label))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Break { value, label }
            }
            origin::ExprKind::Return { value } => {
                let value = {
                    let context = PrintContext {
                        value: value,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Return),
                                "::",
                                stringify!(value)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Return { value }
            }
            origin::ExprKind::Continue { label } => {
                let label = {
                    let context = PrintContext {
                        value: label,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Continue),
                                "::",
                                stringify!(label)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Continue { label }
            }
            origin::ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Closure),
                                "::",
                                stringify!(params)
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
                                stringify!(ExprKind::Closure),
                                "::",
                                stringify!(body)
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
                                stringify!(ExprKind::Closure),
                                "::",
                                stringify!(captures)
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
            origin::ExprKind::Block { body, safety_mode } => {
                let body = {
                    let context = PrintContext {
                        value: body,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ExprKind::Block), "::", stringify!(body))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let safety_mode = {
                    let context = PrintContext {
                        value: safety_mode,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Block),
                                "::",
                                stringify!(safety_mode)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Block { body, safety_mode }
            }
            origin::ExprKind::Quote { contents } => {
                let contents = {
                    let context = PrintContext {
                        value: contents,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Quote),
                                "::",
                                stringify!(contents)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Quote { contents }
            }
            origin::ExprKind::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ExprKind::Error),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ExprKind::Error(anon_field_0)
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GenericParamKind {
    type Out = destination::GenericParamKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
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
                                stringify!(GenericParamKind::Const),
                                "::",
                                stringify!(ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericParamKind::Const { ty }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::TraitGoal {
    type Out = destination::TraitGoal<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::TraitGoal { trait_, args } => {
                let trait_ = {
                    let context = PrintContext {
                        value: trait_,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(TraitGoal), "::", stringify!(trait_))
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
                            position: concat!(stringify!(TraitGoal), "::", stringify!(args)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::TraitGoal { trait_, args }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ImplIdent {
    type Out = destination::ImplIdent<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ImplIdent { goal, name } => {
                let goal = {
                    let context = PrintContext {
                        value: goal,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplIdent), "::", stringify!(goal)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ImplIdent), "::", stringify!(name)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ImplIdent { goal, name }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ProjectionPredicate {
    type Out = destination::ProjectionPredicate<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ProjectionPredicate {
                impl_,
                assoc_item,
                ty,
            } => {
                let impl_ = {
                    let context = PrintContext {
                        value: impl_,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ProjectionPredicate),
                                "::",
                                stringify!(impl_)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let assoc_item = {
                    let context = PrintContext {
                        value: assoc_item,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ProjectionPredicate),
                                "::",
                                stringify!(assoc_item)
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
                                stringify!(ProjectionPredicate),
                                "::",
                                stringify!(ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::GenericConstraint {
    type Out = destination::GenericConstraint<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericConstraint::Lifetime(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(GenericConstraint::Lifetime),
                                "::",
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
                                stringify!(GenericConstraint::Type),
                                "::",
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
                                stringify!(GenericConstraint::Projection),
                                "::",
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::GenericParam { ident, meta, kind } => {
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(GenericParam), "::", stringify!(ident))
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
                            position: concat!(stringify!(GenericParam), "::", stringify!(meta))
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
                            position: concat!(stringify!(GenericParam), "::", stringify!(kind))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::GenericParam { ident, meta, kind }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Generics {
    type Out = destination::Generics<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Generics {
                params,
                constraints,
            } => {
                let params = {
                    let context = PrintContext {
                        value: params,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Generics), "::", stringify!(params))
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
                            position: concat!(stringify!(Generics), "::", stringify!(constraints))
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::SafetyKind::Safe => destination::SafetyKind::Safe,
            origin::SafetyKind::Unsafe => destination::SafetyKind::Unsafe,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Attribute {
    type Out = destination::Attribute<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Attribute { kind, span } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Attribute), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let span = {
                    let context = PrintContext {
                        value: span,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Attribute), "::", stringify!(span)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Attribute { kind, span }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::AttributeKind {
    type Out = destination::AttributeKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::AttributeKind::Tool { path, tokens } => {
                let path = {
                    let context = PrintContext {
                        value: path,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(AttributeKind::Tool),
                                "::",
                                stringify!(path)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let tokens = {
                    let context = PrintContext {
                        value: tokens,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(AttributeKind::Tool),
                                "::",
                                stringify!(tokens)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::AttributeKind::Tool { path, tokens }
            }
            origin::AttributeKind::DocComment { kind, body } => {
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(AttributeKind::DocComment),
                                "::",
                                stringify!(kind)
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
                                stringify!(AttributeKind::DocComment),
                                "::",
                                stringify!(body)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::AttributeKind::DocComment { kind, body }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::DocCommentKind {
    type Out = destination::DocCommentKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::DocCommentKind::Line => destination::DocCommentKind::Line,
            origin::DocCommentKind::Block => destination::DocCommentKind::Block,
        }
    }
}
/// A list of attributes.
pub type Attributes = Vec<Attribute>;
impl<'a> ToPrintView<'a> for origin::SpannedTy {
    type Out = destination::SpannedTy<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::SpannedTy { span, ty } => {
                let span = {
                    let context = PrintContext {
                        value: span,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(SpannedTy), "::", stringify!(span)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(SpannedTy), "::", stringify!(ty)).into(),
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Param {
                pat,
                ty,
                attributes,
            } => {
                let pat = {
                    let context = PrintContext {
                        value: pat,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Param), "::", stringify!(pat)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let ty = {
                    let context = PrintContext {
                        value: ty,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Param), "::", stringify!(ty)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let attributes = {
                    let context = PrintContext {
                        value: attributes,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Param), "::", stringify!(attributes))
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
impl<'a> ToPrintView<'a> for origin::Variant {
    type Out = destination::Variant<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Variant), "::", stringify!(name)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let arguments = {
                    let context = PrintContext {
                        value: arguments,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Variant), "::", stringify!(arguments))
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
                            position: concat!(stringify!(Variant), "::", stringify!(is_record))
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
                            position: concat!(stringify!(Variant), "::", stringify!(attributes))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Variant {
                    name,
                    arguments,
                    is_record,
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Fn), "::", stringify!(name))
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
                            position: concat!(stringify!(ItemKind::Fn), "::", stringify!(generics))
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
                            position: concat!(stringify!(ItemKind::Fn), "::", stringify!(body))
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
                            position: concat!(stringify!(ItemKind::Fn), "::", stringify!(params))
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
                            position: concat!(stringify!(ItemKind::Fn), "::", stringify!(safety))
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
            origin::ItemKind::TyAlias { name, generics, ty } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::TyAlias),
                                "::",
                                stringify!(name)
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
                                stringify!(ItemKind::TyAlias),
                                "::",
                                stringify!(generics)
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
                            position: concat!(stringify!(ItemKind::TyAlias), "::", stringify!(ty))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::TyAlias { name, generics, ty }
            }
            origin::ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Type), "::", stringify!(name))
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
                                stringify!(ItemKind::Type),
                                "::",
                                stringify!(generics)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let variants = {
                    let context = PrintContext {
                        value: variants,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Type),
                                "::",
                                stringify!(variants)
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
                                stringify!(ItemKind::Type),
                                "::",
                                stringify!(is_struct)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                }
            }
            origin::ItemKind::Trait {
                name,
                generics,
                items,
            } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Trait), "::", stringify!(name))
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
                                stringify!(ItemKind::Trait),
                                "::",
                                stringify!(generics)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let items = {
                    let context = PrintContext {
                        value: items,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Trait), "::", stringify!(items))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Trait {
                    name,
                    generics,
                    items,
                }
            }
            origin::ItemKind::Impl {
                generics,
                self_ty,
                of_trait,
                items,
                parent_bounds,
                safety,
            } => {
                let generics = {
                    let context = PrintContext {
                        value: generics,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Impl),
                                "::",
                                stringify!(generics)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let self_ty = {
                    let context = PrintContext {
                        value: self_ty,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Impl),
                                "::",
                                stringify!(self_ty)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let of_trait = {
                    let context = PrintContext {
                        value: of_trait,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Impl),
                                "::",
                                stringify!(of_trait)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let items = {
                    let context = PrintContext {
                        value: items,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Impl), "::", stringify!(items))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let parent_bounds = {
                    let context = PrintContext {
                        value: parent_bounds,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Impl),
                                "::",
                                stringify!(parent_bounds)
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
                            position: concat!(stringify!(ItemKind::Impl), "::", stringify!(safety))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                }
            }
            origin::ItemKind::Alias { name, item } => {
                let name = {
                    let context = PrintContext {
                        value: name,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Alias), "::", stringify!(name))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let item = {
                    let context = PrintContext {
                        value: item,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Alias), "::", stringify!(item))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Alias { name, item }
            }
            origin::ItemKind::Use {
                path,
                is_external,
                rename,
            } => {
                let path = {
                    let context = PrintContext {
                        value: path,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Use), "::", stringify!(path))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let is_external = {
                    let context = PrintContext {
                        value: is_external,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Use),
                                "::",
                                stringify!(is_external)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let rename = {
                    let context = PrintContext {
                        value: rename,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Use), "::", stringify!(rename))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Use {
                    path,
                    is_external,
                    rename,
                }
            }
            origin::ItemKind::Quote { quote, origin } => {
                let quote = {
                    let context = PrintContext {
                        value: quote,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(ItemKind::Quote), "::", stringify!(quote))
                                .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let origin = {
                    let context = PrintContext {
                        value: origin,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Quote),
                                "::",
                                stringify!(origin)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Quote { quote, origin }
            }
            origin::ItemKind::Error(anon_field_0) => {
                let anon_field_0 = {
                    let context = PrintContext {
                        value: anon_field_0,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ItemKind::Error),
                                "::",
                                stringify!(anon_field_0)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ItemKind::Error(anon_field_0)
            }
            origin::ItemKind::NotImplementedYet => destination::ItemKind::NotImplementedYet,
        }
    }
}
impl<'a> ToPrintView<'a> for origin::Item {
    type Out = destination::Item<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::Item { ident, kind, meta } => {
                let ident = {
                    let context = PrintContext {
                        value: ident,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(ident)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let kind = {
                    let context = PrintContext {
                        value: kind,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(kind)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                let meta = {
                    let context = PrintContext {
                        value: meta,
                        payload: PrintContextPayload {
                            position: concat!(stringify!(Item), "::", stringify!(meta)).into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::Item { ident, kind, meta }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ResugaredExprKind {
    type Out = destination::ResugaredExprKind<'a>;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
    ) -> Self::Out {
        match self {
            origin::ResugaredExprKind::ConstantApp { constant, generics } => {
                let constant = {
                    let context = PrintContext {
                        value: constant,
                        payload: PrintContextPayload {
                            position: concat!(
                                stringify!(ResugaredExprKind::ConstantApp),
                                "::",
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
                                stringify!(ResugaredExprKind::ConstantApp),
                                "::",
                                stringify!(generics)
                            )
                            .into(),
                            parent: parent_context.clone(),
                        },
                    };
                    context
                };
                destination::ResugaredExprKind::ConstantApp { constant, generics }
            }
        }
    }
}
impl<'a> ToPrintView<'a> for origin::ResugaredPatKind {
    type Out = destination::ResugaredPatKind;
    fn to_print_view(
        &'a self,
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
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
        #[allow(unused_variables)] parent_context: Option<std::rc::Rc<ParentPrintContext<'a>>>,
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
