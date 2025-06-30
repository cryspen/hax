pub mod map_reduce_cf_diag {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapReduceCfDiag: HasSpan {
        type Error;
        type Out: Monoid;
        fn visit_global_id(
            &mut self,
            v: &mut GlobalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_global_id(self, v, visitor_diagnostic_set)
        }
        fn visit_local_id(
            &mut self,
            v: &mut LocalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_local_id(self, v, visitor_diagnostic_set)
        }
        fn visit_int_size(
            &mut self,
            v: &mut IntSize,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_size(self, v, visitor_diagnostic_set)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_signedness(self, v, visitor_diagnostic_set)
        }
        fn visit_int_kind(
            &mut self,
            v: &mut IntKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_float_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_literal(
            &mut self,
            v: &mut Literal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_literal(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_span(
            &mut self,
            v: &mut Span,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_span(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_value(self, v, visitor_diagnostic_set)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_primitive_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_region(self, v, visitor_diagnostic_set)
        }
        fn visit_ty(
            &mut self,
            v: &mut Ty,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_error_node(self, v, visitor_diagnostic_set)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_dyn_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_metadata(self, v, visitor_diagnostic_set)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat(self, v)
        }
        fn visit_arm(
            &mut self,
            v: &mut Arm,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_arm(self, v, visitor_diagnostic_set)
        }
        fn visit_guard(
            &mut self,
            v: &mut Guard,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard(self, v, visitor_diagnostic_set)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_borrow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_binding_mode(self, v, visitor_diagnostic_set)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_lhs(
            &mut self,
            v: &mut Lhs,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_lhs(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote_content(self, v, visitor_diagnostic_set)
        }
        fn visit_quote(
            &mut self,
            v: &mut Quote,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_position(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_control_flow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_state(self, v, visitor_diagnostic_set)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_ident(self, v, visitor_diagnostic_set)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_projection_predicate(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_constraint(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param(self, v, visitor_diagnostic_set)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generics(self, v, visitor_diagnostic_set)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_safety_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_doc_comment_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_spanned_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_param(
            &mut self,
            v: &mut Param,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_param(self, v, visitor_diagnostic_set)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_variant(self, v, visitor_diagnostic_set)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item(&mut self, v: &mut Item) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_signedness(signedness, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_float_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_int_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_float_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty_kind(anon_field_0.deref_mut(), visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_primitive_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value
                            .append(visitor.visit_ty(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value
                            .append(visitor.visit_ty(visitor_item, visitor_diagnostic_set)?);
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_region(region, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_local_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_expr(length.deref_mut())?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(
                            visitor.visit_dyn_trait_goal(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_ty_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(trait_, visitor_diagnostic_set)?;
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Expr { kind, ty, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_expr_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Pat { kind, ty, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_pat_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                visitor_reduce_value.append(visitor.visit_expr(body)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind, visitor_diagnostic_set)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_borrow_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value
                        .append(visitor.visit_spanned_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_binding_mode(mode, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(constructor, visitor_diagnostic_set)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?,
                            );
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_pat_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(field, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(visitor.visit_expr(index)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_trait_goal(goal, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::LocalBound { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_impl_ident(ident, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set)?);
                    visitor_reduce_value
                        .append(visitor.visit_impl_ident(ident, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor_reduce_value
                            .append(visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                visitor_reduce_value
                    .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                visitor_reduce_value
                    .append(visitor.visit_impl_item_kind(kind, visitor_diagnostic_set)?);
                visitor_reduce_value
                    .append(visitor.visit_global_id(ident, visitor_diagnostic_set)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set)?,
                            );
                            visitor_reduce_value.append(
                                visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set)?,
                            );
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor
                        .visit_resugared_impl_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                visitor_reduce_value
                    .append(visitor.visit_trait_item_kind(kind, visitor_diagnostic_set)?);
                visitor_reduce_value
                    .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                visitor_reduce_value
                    .append(visitor.visit_global_id(ident, visitor_diagnostic_set)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(
                            visitor.visit_impl_ident(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor
                        .visit_resugared_trait_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(
                            visitor.visit_quote_content(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_item_quote_origin_kind(item_kind, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item_ident, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(
                        visitor
                            .visit_item_quote_origin_position(position, visitor_diagnostic_set)?,
                    );
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::TyAlias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::MacroInvocation { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Trait { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Impl { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Alias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Use { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Quote { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::HaxError { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::After { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::Replace { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_expr(iterator)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start)?;
                    visitor_reduce_value.append(visitor.visit_expr(end)?);
                    visitor_reduce_value
                        .append(visitor.visit_local_id(var, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(visitor.visit_ty(var_ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ControlFlowKind::BreakOrReturn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init)?;
                    visitor_reduce_value.append(visitor.visit_pat(body_pat)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    visitor_reduce_value.append(visitor.visit_expr(then)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value
                            .append(visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_literal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(constructor, visitor_diagnostic_set)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?,
                            );
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor_reduce_value
                            .append(visitor.visit_arm(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_local_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_expr(value)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value
                        .append(visitor.visit_loop_kind(kind, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety_mode, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_expr_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(trait_, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_trait_goal(goal, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_global_id(assoc_item, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_ident(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_projection_predicate(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident, visitor_diagnostic_set)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                visitor_reduce_value
                    .append(visitor.visit_generic_param_kind(kind, visitor_diagnostic_set)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(
                            visitor.visit_generic_param(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value.append(
                            visitor
                                .visit_generic_constraint(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_attribute_kind(kind, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_span(span, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_doc_comment_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?,
                            );
                            visitor_reduce_value
                                .append(visitor.visit_ty(visitor_item_1, visitor_diagnostic_set)?);
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set)?);
                    }
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                    for visitor_item in variants {
                        visitor_reduce_value
                            .append(visitor.visit_variant(visitor_item, visitor_diagnostic_set)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set)?);
                    for visitor_item in items {
                        visitor_reduce_value.append(
                            visitor.visit_trait_item(visitor_item, visitor_diagnostic_set)?,
                        );
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    visitor_reduce_value.append(visitor.visit_ty(self_ty, visitor_diagnostic_set)?);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?,
                        );
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(
                                visitor
                                    .visit_generic_value(visitor_item, visitor_diagnostic_set)?,
                            );
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value
                            .append(visitor.visit_impl_item(visitor_item, visitor_diagnostic_set)?);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set)?,
                            );
                            visitor_reduce_value.append(
                                visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set)?,
                            );
                        };
                    }
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_item_quote_origin(origin, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduceCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Item { ident, kind, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(ident, visitor_diagnostic_set)?;
                    visitor_reduce_value
                        .append(visitor.visit_item_kind(kind, visitor_diagnostic_set)?);
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
}
pub mod map_cf_diag {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapCfDiag: HasSpan {
        type Error;
        fn visit_global_id(
            &mut self,
            v: &mut GlobalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_global_id(self, v, visitor_diagnostic_set)
        }
        fn visit_local_id(
            &mut self,
            v: &mut LocalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_local_id(self, v, visitor_diagnostic_set)
        }
        fn visit_int_size(
            &mut self,
            v: &mut IntSize,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_size(self, v, visitor_diagnostic_set)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_signedness(self, v, visitor_diagnostic_set)
        }
        fn visit_int_kind(
            &mut self,
            v: &mut IntKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_float_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_literal(
            &mut self,
            v: &mut Literal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_literal(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_span(
            &mut self,
            v: &mut Span,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_span(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_value(self, v, visitor_diagnostic_set)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_primitive_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_region(self, v, visitor_diagnostic_set)
        }
        fn visit_ty(
            &mut self,
            v: &mut Ty,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_error_node(self, v, visitor_diagnostic_set)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_dyn_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_metadata(self, v, visitor_diagnostic_set)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat(self, v)
        }
        fn visit_arm(
            &mut self,
            v: &mut Arm,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_arm(self, v, visitor_diagnostic_set)
        }
        fn visit_guard(
            &mut self,
            v: &mut Guard,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard(self, v, visitor_diagnostic_set)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_borrow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_binding_mode(self, v, visitor_diagnostic_set)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_lhs(
            &mut self,
            v: &mut Lhs,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_lhs(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote_content(self, v, visitor_diagnostic_set)
        }
        fn visit_quote(
            &mut self,
            v: &mut Quote,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_position(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_control_flow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_state(self, v, visitor_diagnostic_set)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_ident(self, v, visitor_diagnostic_set)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_projection_predicate(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_constraint(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param(self, v, visitor_diagnostic_set)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generics(self, v, visitor_diagnostic_set)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_safety_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_doc_comment_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_spanned_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_param(
            &mut self,
            v: &mut Param,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_param(self, v, visitor_diagnostic_set)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_variant(self, v, visitor_diagnostic_set)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item(&mut self, v: &mut Item) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size, visitor_diagnostic_set)?;
                    visitor.visit_signedness(signedness, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref_mut(), visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item, visitor_diagnostic_set)?;
                    }
                    visitor.visit_ty(output, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner, visitor_diagnostic_set)?;
                    visitor.visit_region(region, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor.visit_expr(length.deref_mut())?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(()),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor.visit_global_id(item, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_, visitor_diagnostic_set)?;
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Expr { kind, ty, meta } => {
                    visitor.visit_expr_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Pat { kind, ty, meta } => {
                    visitor.visit_pat_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat)?;
                visitor.visit_expr(body)?;
                visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind, visitor_diagnostic_set)?;
                visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(()),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(()),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_spanned_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var, visitor_diagnostic_set)?;
                    visitor.visit_binding_mode(mode, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor, visitor_diagnostic_set)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?;
                            visitor.visit_pat(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var, visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor.visit_global_id(field, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    visitor.visit_expr(index)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref_mut(), visitor_diagnostic_set)?;
                    visitor.visit_trait_goal(goal, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor.visit_impl_ident(ident, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor.visit_global_id(item, visitor_diagnostic_set)?;
                    visitor.visit_impl_ident(ident, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                visitor.visit_generics(generics, visitor_diagnostic_set)?;
                visitor.visit_impl_item_kind(kind, visitor_diagnostic_set)?;
                visitor.visit_global_id(ident, visitor_diagnostic_set)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set)?;
                            visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                visitor.visit_trait_item_kind(kind, visitor_diagnostic_set)?;
                visitor.visit_generics(generics, visitor_diagnostic_set)?;
                visitor.visit_global_id(ident, visitor_diagnostic_set)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set)?;
                    }
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor
                        .visit_resugared_trait_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(()),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind, visitor_diagnostic_set)?;
                    visitor.visit_global_id(item_ident, visitor_diagnostic_set)?;
                    visitor.visit_item_quote_origin_position(position, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::TyAlias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::MacroInvocation { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Trait { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Alias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Quote { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::HaxError { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::Replace { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => std::ops::ControlFlow::Continue(()),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_expr(iterator)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start)?;
                    visitor.visit_expr(end)?;
                    visitor.visit_local_id(var, visitor_diagnostic_set)?;
                    visitor.visit_ty(var_ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
                ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init)?;
                    visitor.visit_pat(body_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition)?;
                    visitor.visit_expr(then)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item)?;
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?;
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor, visitor_diagnostic_set)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?;
                            visitor.visit_expr(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs, visitor_diagnostic_set)?;
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_loop_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item)?;
                    }
                    visitor.visit_expr(body)?;
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_safety_kind(safety_mode, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_, visitor_diagnostic_set)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set)?;
                    visitor.visit_global_id(assoc_item, visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident, visitor_diagnostic_set)?;
                visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                visitor.visit_generic_param_kind(kind, visitor_diagnostic_set)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item, visitor_diagnostic_set)?;
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind, visitor_diagnostic_set)?;
                    visitor.visit_span(span, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(()),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span, visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?;
                            visitor.visit_ty(visitor_item_1, visitor_diagnostic_set)?;
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set)?;
                    }
                    visitor.visit_safety_kind(safety, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    visitor.visit_ty(ty, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item, visitor_diagnostic_set)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics, visitor_diagnostic_set)?;
                    visitor.visit_ty(self_ty, visitor_diagnostic_set)?;
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set)?;
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set)?;
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item, visitor_diagnostic_set)?;
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set)?;
                            visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set)?;
                        };
                    }
                    visitor.visit_safety_kind(safety, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set)?;
                    visitor.visit_global_id(item, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote, visitor_diagnostic_set)?;
                    visitor.visit_item_quote_origin(origin, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapCfDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Item { ident, kind, meta } => {
                    visitor.visit_global_id(ident, visitor_diagnostic_set)?;
                    visitor.visit_item_kind(kind, visitor_diagnostic_set)?;
                    visitor.visit_metadata(meta, visitor_diagnostic_set)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
}
pub mod map_reduce_diag {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait MapReduceDiag: HasSpan {
        type Out: Monoid;
        fn visit_global_id(
            &mut self,
            v: &mut GlobalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_global_id(self, v, visitor_diagnostic_set)
        }
        fn visit_local_id(
            &mut self,
            v: &mut LocalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_local_id(self, v, visitor_diagnostic_set)
        }
        fn visit_int_size(
            &mut self,
            v: &mut IntSize,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_int_size(self, v, visitor_diagnostic_set)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_signedness(self, v, visitor_diagnostic_set)
        }
        fn visit_int_kind(
            &mut self,
            v: &mut IntKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_int_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_float_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_literal(
            &mut self,
            v: &mut Literal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_literal(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_resugared_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_span(
            &mut self,
            v: &mut Span,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_span(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_generic_value(self, v, visitor_diagnostic_set)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_primitive_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_region(self, v, visitor_diagnostic_set)
        }
        fn visit_ty(
            &mut self,
            v: &mut Ty,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_error_node(self, v, visitor_diagnostic_set)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_dyn_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_metadata(self, v, visitor_diagnostic_set)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> Self::Out {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> Self::Out {
            visit_pat(self, v)
        }
        fn visit_arm(
            &mut self,
            v: &mut Arm,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_arm(self, v, visitor_diagnostic_set)
        }
        fn visit_guard(
            &mut self,
            v: &mut Guard,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_guard(self, v, visitor_diagnostic_set)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_borrow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_binding_mode(self, v, visitor_diagnostic_set)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_guard_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_lhs(
            &mut self,
            v: &mut Lhs,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_lhs(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_impl_expr(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_impl_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_impl_item(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_trait_item(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_quote_content(self, v, visitor_diagnostic_set)
        }
        fn visit_quote(
            &mut self,
            v: &mut Quote,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_quote(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_item_quote_origin(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_item_quote_origin_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_item_quote_origin_position(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_loop_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_control_flow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_loop_state(self, v, visitor_diagnostic_set)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_generic_param_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_impl_ident(self, v, visitor_diagnostic_set)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_projection_predicate(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_generic_constraint(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_generic_param(self, v, visitor_diagnostic_set)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_generics(self, v, visitor_diagnostic_set)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_safety_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_attribute(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_attribute_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_doc_comment_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_spanned_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_param(
            &mut self,
            v: &mut Param,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_param(self, v, visitor_diagnostic_set)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_variant(self, v, visitor_diagnostic_set)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> Self::Out {
            visit_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item(&mut self, v: &mut Item) -> Self::Out {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                IntSize::S8 { .. } => V::Out::identity(),
                IntSize::S16 { .. } => V::Out::identity(),
                IntSize::S32 { .. } => V::Out::identity(),
                IntSize::S64 { .. } => V::Out::identity(),
                IntSize::S128 { .. } => V::Out::identity(),
                IntSize::SSize { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Signedness::Signed { .. } => V::Out::identity(),
                Signedness::Unsigned { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_signedness(signedness, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                FloatKind::F16 { .. } => V::Out::identity(),
                FloatKind::F32 { .. } => V::Out::identity(),
                FloatKind::F64 { .. } => V::Out::identity(),
                FloatKind::F128 { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Literal::String { .. } => V::Out::identity(),
                Literal::Char { .. } => V::Out::identity(),
                Literal::Bool { .. } => V::Out::identity(),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(kind, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                GenericValue::Lifetime { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => V::Out::identity(),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_int_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_float_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                PrimitiveTy::Char { .. } => V::Out::identity(),
                PrimitiveTy::Str { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Region { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_ty_kind(anon_field_0.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_primitive_ty(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value
                            .append(visitor.visit_ty(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value
                            .append(visitor.visit_ty(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_region(region, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_local_id(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_expr(length.deref_mut()));
                    visitor_reduce_value
                }
                TyKind::RawPointer { .. } => V::Out::identity(),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(
                            visitor.visit_dyn_trait_goal(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_ty_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_, visitor_diagnostic_set);
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> V::Out {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Expr { kind, ty, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_expr_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduceDiag + ?Sized + HasSpan>(visitor: &mut V, v: &mut Pat) -> V::Out {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Pat { kind, ty, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_pat_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat);
                visitor_reduce_value.append(visitor.visit_expr(body));
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind, visitor_diagnostic_set);
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                BorrowKind::Shared { .. } => V::Out::identity(),
                BorrowKind::Unique { .. } => V::Out::identity(),
                BorrowKind::Mut { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                BindingMode::ByValue { .. } => V::Out::identity(),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_borrow_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                PatKind::Wild { .. } => V::Out::identity(),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value
                        .append(visitor.visit_spanned_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat);
                    visitor_reduce_value
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_binding_mode(mode, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(constructor, visitor_diagnostic_set);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set),
                            );
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_pat_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut());
                    visitor_reduce_value
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                        .append(visitor.visit_global_id(field, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value.append(visitor.visit_expr(index));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_expr_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_trait_goal(goal, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => V::Out::identity(),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ImplExprKind::LocalBound { .. } => V::Out::identity(),
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_impl_ident(ident, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set));
                    visitor_reduce_value
                        .append(visitor.visit_impl_ident(ident, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor_reduce_value
                            .append(visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ImplExprKind::Dyn { .. } => V::Out::identity(),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta, visitor_diagnostic_set);
                visitor_reduce_value
                    .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                visitor_reduce_value
                    .append(visitor.visit_impl_item_kind(kind, visitor_diagnostic_set));
                visitor_reduce_value.append(visitor.visit_global_id(ident, visitor_diagnostic_set));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set),
                            );
                            visitor_reduce_value.append(
                                visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set),
                            );
                        };
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor
                        .visit_resugared_impl_item_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta, visitor_diagnostic_set);
                visitor_reduce_value
                    .append(visitor.visit_trait_item_kind(kind, visitor_diagnostic_set));
                visitor_reduce_value
                    .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                visitor_reduce_value.append(visitor.visit_global_id(ident, visitor_diagnostic_set));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value
                            .append(visitor.visit_impl_ident(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor
                        .visit_resugared_trait_item_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => V::Out::identity(),
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(
                            visitor.visit_quote_content(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_item_quote_origin_kind(item_kind, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item_ident, visitor_diagnostic_set));
                    visitor_reduce_value.append(
                        visitor.visit_item_quote_origin_position(position, visitor_diagnostic_set),
                    );
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => V::Out::identity(),
                ItemQuoteOriginKind::TyAlias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Type { .. } => V::Out::identity(),
                ItemQuoteOriginKind::MacroInvocation { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Trait { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Impl { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Alias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Use { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Quote { .. } => V::Out::identity(),
                ItemQuoteOriginKind::HaxError { .. } => V::Out::identity(),
                ItemQuoteOriginKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::After { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::Replace { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => V::Out::identity(),
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_expr(iterator));
                    visitor_reduce_value
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start);
                    visitor_reduce_value.append(visitor.visit_expr(end));
                    visitor_reduce_value
                        .append(visitor.visit_local_id(var, visitor_diagnostic_set));
                    visitor_reduce_value.append(visitor.visit_ty(var_ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => V::Out::identity(),
                ControlFlowKind::BreakOrReturn { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init);
                    visitor_reduce_value.append(visitor.visit_pat(body_pat));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value.append(visitor.visit_expr(then));
                    visitor_reduce_value
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value
                            .append(visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_literal(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(constructor, visitor_diagnostic_set);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set),
                            );
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor_reduce_value
                            .append(visitor.visit_arm(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_global_id(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_local_id(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_expr(value));
                    visitor_reduce_value
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value
                        .append(visitor.visit_loop_kind(kind, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Continue { .. } => V::Out::identity(),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety_mode, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_expr_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => V::Out::identity(),
                GenericParamKind::Type { .. } => V::Out::identity(),
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor_reduce_value.append(
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(goal, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(assoc_item, visitor_diagnostic_set));
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => V::Out::identity(),
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_impl_ident(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_projection_predicate(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident, visitor_diagnostic_set);
                visitor_reduce_value.append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                visitor_reduce_value
                    .append(visitor.visit_generic_param_kind(kind, visitor_diagnostic_set));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(
                            visitor.visit_generic_param(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value.append(
                            visitor.visit_generic_constraint(visitor_item, visitor_diagnostic_set),
                        );
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                SafetyKind::Safe { .. } => V::Out::identity(),
                SafetyKind::Unsafe { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_attribute_kind(kind, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_span(span, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                AttributeKind::Tool { .. } => V::Out::identity(),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_doc_comment_kind(kind, visitor_diagnostic_set);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                DocCommentKind::Line { .. } => V::Out::identity(),
                DocCommentKind::Block { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set),
                            );
                            visitor_reduce_value
                                .append(visitor.visit_ty(visitor_item_1, visitor_diagnostic_set));
                            ();
                        };
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> V::Out {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in params {
                        visitor_reduce_value
                            .append(visitor.visit_param(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                    visitor_reduce_value.append(visitor.visit_ty(ty, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                    for visitor_item in variants {
                        visitor_reduce_value
                            .append(visitor.visit_variant(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_generics(generics, visitor_diagnostic_set));
                    for visitor_item in items {
                        visitor_reduce_value
                            .append(visitor.visit_trait_item(visitor_item, visitor_diagnostic_set));
                    }
                    visitor_reduce_value
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_generics(generics, visitor_diagnostic_set);
                    visitor_reduce_value.append(visitor.visit_ty(self_ty, visitor_diagnostic_set));
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set),
                        );
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(
                                visitor.visit_generic_value(visitor_item, visitor_diagnostic_set),
                            );
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value
                            .append(visitor.visit_impl_item(visitor_item, visitor_diagnostic_set));
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(
                                visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set),
                            );
                            visitor_reduce_value.append(
                                visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set),
                            );
                        };
                    }
                    visitor_reduce_value
                        .append(visitor.visit_safety_kind(safety, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_global_id(item, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ItemKind::Use { .. } => V::Out::identity(),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_item_quote_origin(origin, visitor_diagnostic_set));
                    visitor_reduce_value
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value =
                        visitor.visit_resugared_item_kind(anon_field_0, visitor_diagnostic_set);
                    visitor_reduce_value
                }
                ItemKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduceDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Item,
    ) -> V::Out {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Item { ident, kind, meta } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(ident, visitor_diagnostic_set);
                    visitor_reduce_value
                        .append(visitor.visit_item_kind(kind, visitor_diagnostic_set));
                    visitor_reduce_value
                        .append(visitor.visit_metadata(meta, visitor_diagnostic_set));
                    visitor_reduce_value
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
}
pub mod map_diag {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait MapDiag: HasSpan {
        fn visit_global_id(
            &mut self,
            v: &mut GlobalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_global_id(self, v, visitor_diagnostic_set)
        }
        fn visit_local_id(
            &mut self,
            v: &mut LocalId,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_local_id(self, v, visitor_diagnostic_set)
        }
        fn visit_int_size(
            &mut self,
            v: &mut IntSize,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_int_size(self, v, visitor_diagnostic_set)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_signedness(self, v, visitor_diagnostic_set)
        }
        fn visit_int_kind(
            &mut self,
            v: &mut IntKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_int_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_float_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_literal(
            &mut self,
            v: &mut Literal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_literal(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_resugared_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_span(&mut self, v: &mut Span, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_span(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_generic_value(self, v, visitor_diagnostic_set)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_primitive_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_region(self, v, visitor_diagnostic_set)
        }
        fn visit_ty(&mut self, v: &mut Ty, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_ty_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_error_node(self, v, visitor_diagnostic_set)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_dyn_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_metadata(self, v, visitor_diagnostic_set)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> () {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> () {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_arm(self, v, visitor_diagnostic_set)
        }
        fn visit_guard(&mut self, v: &mut Guard, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_guard(self, v, visitor_diagnostic_set)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_borrow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_binding_mode(self, v, visitor_diagnostic_set)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_pat_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_guard_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_lhs(&mut self, v: &mut Lhs, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_lhs(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_impl_expr(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_impl_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_impl_item(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_impl_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_trait_item(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_trait_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_quote_content(self, v, visitor_diagnostic_set)
        }
        fn visit_quote(&mut self, v: &mut Quote, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_quote(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_item_quote_origin(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_item_quote_origin_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_item_quote_origin_position(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_loop_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_control_flow_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_loop_state(self, v, visitor_diagnostic_set)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_expr_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_generic_param_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_trait_goal(self, v, visitor_diagnostic_set)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_impl_ident(self, v, visitor_diagnostic_set)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_projection_predicate(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_generic_constraint(self, v, visitor_diagnostic_set)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_generic_param(self, v, visitor_diagnostic_set)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_generics(self, v, visitor_diagnostic_set)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_safety_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_attribute(self, v, visitor_diagnostic_set)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_attribute_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_doc_comment_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_spanned_ty(self, v, visitor_diagnostic_set)
        }
        fn visit_param(&mut self, v: &mut Param, visitor_diagnostic_set: &mut DiagnosticSet) -> () {
            visit_param(self, v, visitor_diagnostic_set)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_variant(self, v, visitor_diagnostic_set)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
            visitor_diagnostic_set: &mut DiagnosticSet,
        ) -> () {
            visit_item_kind(self, v, visitor_diagnostic_set)
        }
        fn visit_item(&mut self, v: &mut Item) -> () {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                IntSize::S8 { .. } => (),
                IntSize::S16 { .. } => (),
                IntSize::S32 { .. } => (),
                IntSize::S64 { .. } => (),
                IntSize::S128 { .. } => (),
                IntSize::SSize { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Signedness::Signed { .. } => (),
                Signedness::Unsigned { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size, visitor_diagnostic_set);
                    visitor.visit_signedness(signedness, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                FloatKind::F16 { .. } => (),
                FloatKind::F32 { .. } => (),
                FloatKind::F64 { .. } => (),
                FloatKind::F128 { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Literal::String { .. } => (),
                Literal::Char { .. } => (),
                Literal::Bool { .. } => (),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind, visitor_diagnostic_set);
                    ()
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                GenericValue::Lifetime { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => (),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                PrimitiveTy::Char { .. } => (),
                PrimitiveTy::Str { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Region { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref_mut(), visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item, visitor_diagnostic_set);
                    }
                    visitor.visit_ty(output, visitor_diagnostic_set);
                    ()
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner, visitor_diagnostic_set);
                    visitor.visit_region(region, visitor_diagnostic_set);
                    ()
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor.visit_expr(length.deref_mut());
                    ()
                }
                TyKind::RawPointer { .. } => (),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor.visit_global_id(item, visitor_diagnostic_set);
                    ()
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_, visitor_diagnostic_set);
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapDiag + ?Sized + HasSpan>(visitor: &mut V, v: &mut Expr) -> () {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Expr { kind, ty, meta } => {
                    visitor.visit_expr_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor.visit_metadata(meta, visitor_diagnostic_set);
                    ()
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapDiag + ?Sized + HasSpan>(visitor: &mut V, v: &mut Pat) -> () {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Pat { kind, ty, meta } => {
                    visitor.visit_pat_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor.visit_metadata(meta, visitor_diagnostic_set);
                    ()
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat);
                visitor.visit_expr(body);
                visitor.visit_metadata(meta, visitor_diagnostic_set);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind, visitor_diagnostic_set);
                visitor.visit_metadata(meta, visitor_diagnostic_set);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                BorrowKind::Shared { .. } => (),
                BorrowKind::Unique { .. } => (),
                BorrowKind::Mut { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                BindingMode::ByValue { .. } => (),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                PatKind::Wild { .. } => (),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat);
                    visitor.visit_spanned_ty(ty, visitor_diagnostic_set);
                    ()
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat);
                    ()
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit, visitor_diagnostic_set);
                    ()
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var, visitor_diagnostic_set);
                    visitor.visit_binding_mode(mode, visitor_diagnostic_set);
                    ()
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor, visitor_diagnostic_set);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set);
                            visitor.visit_pat(visitor_item_1);
                        };
                    }
                    ()
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var, visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref_mut());
                    ()
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor.visit_global_id(field, visitor_diagnostic_set);
                    ()
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref_mut(), visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    visitor.visit_expr(index);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref_mut(), visitor_diagnostic_set);
                    visitor.visit_trait_goal(goal, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => (),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ImplExprKind::LocalBound { .. } => (),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor.visit_impl_ident(ident, visitor_diagnostic_set);
                    ()
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor.visit_global_id(item, visitor_diagnostic_set);
                    visitor.visit_impl_ident(ident, visitor_diagnostic_set);
                    ()
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ImplExprKind::Dyn { .. } => (),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta, visitor_diagnostic_set);
                visitor.visit_generics(generics, visitor_diagnostic_set);
                visitor.visit_impl_item_kind(kind, visitor_diagnostic_set);
                visitor.visit_global_id(ident, visitor_diagnostic_set);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set);
                            visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set);
                        };
                    }
                    ()
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta, visitor_diagnostic_set);
                visitor.visit_trait_item_kind(kind, visitor_diagnostic_set);
                visitor.visit_generics(generics, visitor_diagnostic_set);
                visitor.visit_global_id(ident, visitor_diagnostic_set);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set);
                    }
                    visitor.visit_expr(body);
                    ()
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_trait_item_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => (),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0);
                    ()
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind, visitor_diagnostic_set);
                    visitor.visit_global_id(item_ident, visitor_diagnostic_set);
                    visitor.visit_item_quote_origin_position(position, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => (),
                ItemQuoteOriginKind::TyAlias { .. } => (),
                ItemQuoteOriginKind::Type { .. } => (),
                ItemQuoteOriginKind::MacroInvocation { .. } => (),
                ItemQuoteOriginKind::Trait { .. } => (),
                ItemQuoteOriginKind::Impl { .. } => (),
                ItemQuoteOriginKind::Alias { .. } => (),
                ItemQuoteOriginKind::Use { .. } => (),
                ItemQuoteOriginKind::Quote { .. } => (),
                ItemQuoteOriginKind::HaxError { .. } => (),
                ItemQuoteOriginKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => (),
                ItemQuoteOriginPosition::After { .. } => (),
                ItemQuoteOriginPosition::Replace { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => (),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition);
                    ()
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat);
                    visitor.visit_expr(iterator);
                    ()
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start);
                    visitor.visit_expr(end);
                    visitor.visit_local_id(var, visitor_diagnostic_set);
                    visitor.visit_ty(var_ty, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => (),
                ControlFlowKind::BreakOrReturn { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init);
                    visitor.visit_pat(body_pat);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition);
                    visitor.visit_expr(then);
                    ()
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item);
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set);
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor, visitor_diagnostic_set);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set);
                            visitor.visit_expr(visitor_item_1);
                        };
                    }
                    ()
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    visitor.visit_expr(body);
                    ()
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs, visitor_diagnostic_set);
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body);
                    visitor.visit_loop_kind(kind, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Continue { .. } => (),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item);
                    }
                    visitor.visit_expr(body);
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body);
                    visitor.visit_safety_kind(safety_mode, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => (),
                GenericParamKind::Type { .. } => (),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_, visitor_diagnostic_set);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_, visitor_diagnostic_set);
                    visitor.visit_global_id(assoc_item, visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => (),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident, visitor_diagnostic_set);
                visitor.visit_metadata(meta, visitor_diagnostic_set);
                visitor.visit_generic_param_kind(kind, visitor_diagnostic_set);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item, visitor_diagnostic_set);
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                SafetyKind::Safe { .. } => (),
                SafetyKind::Unsafe { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind, visitor_diagnostic_set);
                    visitor.visit_span(span, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                AttributeKind::Tool { .. } => (),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                DocCommentKind::Line { .. } => (),
                DocCommentKind::Block { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span, visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set);
                            visitor.visit_ty(visitor_item_1, visitor_diagnostic_set);
                            ();
                        };
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapDiag + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
        visitor_diagnostic_set: &mut DiagnosticSet,
    ) -> () {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor.visit_generics(generics, visitor_diagnostic_set);
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item, visitor_diagnostic_set);
                    }
                    visitor.visit_safety_kind(safety, visitor_diagnostic_set);
                    ()
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor.visit_generics(generics, visitor_diagnostic_set);
                    visitor.visit_ty(ty, visitor_diagnostic_set);
                    ()
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor.visit_generics(generics, visitor_diagnostic_set);
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor.visit_generics(generics, visitor_diagnostic_set);
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item, visitor_diagnostic_set);
                    }
                    ()
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics, visitor_diagnostic_set);
                    visitor.visit_ty(self_ty, visitor_diagnostic_set);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0, visitor_diagnostic_set);
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item, visitor_diagnostic_set);
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item, visitor_diagnostic_set);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0, visitor_diagnostic_set);
                            visitor.visit_impl_ident(visitor_item_1, visitor_diagnostic_set);
                        };
                    }
                    visitor.visit_safety_kind(safety, visitor_diagnostic_set);
                    ()
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name, visitor_diagnostic_set);
                    visitor.visit_global_id(item, visitor_diagnostic_set);
                    ()
                }
                ItemKind::Use { .. } => (),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote, visitor_diagnostic_set);
                    visitor.visit_item_quote_origin(origin, visitor_diagnostic_set);
                    ()
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0, visitor_diagnostic_set);
                    ()
                }
                ItemKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapDiag + ?Sized + HasSpan>(visitor: &mut V, v: &mut Item) -> () {
        let mut visitor_diagnostic_set = DiagnosticSet::default();
        let result = with_span(visitor, v.span(), |visitor| {
            let visitor_diagnostic_set = &mut visitor_diagnostic_set;
            match v {
                Item { ident, kind, meta } => {
                    visitor.visit_global_id(ident, visitor_diagnostic_set);
                    visitor.visit_item_kind(kind, visitor_diagnostic_set);
                    visitor.visit_metadata(meta, visitor_diagnostic_set);
                    ()
                }
            }
        });
        v.handle_diagnostics(visitor_diagnostic_set);
        result
    }
}
pub mod map_reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapReduceCf: HasSpan {
        type Error;
        type Out: Monoid;
        fn visit_global_id(
            &mut self,
            v: &mut GlobalId,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_global_id(self, v)
        }
        fn visit_local_id(
            &mut self,
            v: &mut LocalId,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_local_id(self, v)
        }
        fn visit_int_size(
            &mut self,
            v: &mut IntSize,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_size(self, v)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_signedness(self, v)
        }
        fn visit_int_kind(
            &mut self,
            v: &mut IntKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_float_kind(self, v)
        }
        fn visit_literal(
            &mut self,
            v: &mut Literal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &mut Span) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_span(self, v)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &mut Ty) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &mut Guard) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &mut Lhs) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &mut Quote) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param(self, v)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &mut Param) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_param(self, v)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_variant(self, v)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &mut Item) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size)?;
                    visitor_reduce_value.append(visitor.visit_signedness(signedness)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner)?;
                    visitor_reduce_value.append(visitor.visit_region(region)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    visitor_reduce_value.append(visitor.visit_expr(length.deref_mut())?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_dyn_trait_goal(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_ty_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_)?;
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                visitor_reduce_value.append(visitor.visit_expr(body)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_spanned_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var)?;
                    visitor_reduce_value.append(visitor.visit_binding_mode(mode)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_pat_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut())?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    visitor_reduce_value.append(visitor.visit_global_id(field)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut())?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    visitor_reduce_value.append(visitor.visit_expr(index)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut())?;
                    visitor_reduce_value.append(visitor.visit_trait_goal(goal)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::LocalBound { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                visitor_reduce_value.append(visitor.visit_generics(generics)?);
                visitor_reduce_value.append(visitor.visit_impl_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_global_id(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_impl_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                visitor_reduce_value.append(visitor.visit_trait_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_generics(generics)?);
                visitor_reduce_value.append(visitor.visit_global_id(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_trait_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_quote_content(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item_ident)?);
                    visitor_reduce_value
                        .append(visitor.visit_item_quote_origin_position(position)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::TyAlias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::MacroInvocation { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Trait { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Impl { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Alias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Use { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Quote { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::HaxError { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::After { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::Replace { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_expr(iterator)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start)?;
                    visitor_reduce_value.append(visitor.visit_expr(end)?);
                    visitor_reduce_value.append(visitor.visit_local_id(var)?);
                    visitor_reduce_value.append(visitor.visit_ty(var_ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ControlFlowKind::BreakOrReturn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init)?;
                    visitor_reduce_value.append(visitor.visit_pat(body_pat)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    visitor_reduce_value.append(visitor.visit_expr(then)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor_reduce_value.append(visitor.visit_arm(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(value)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value.append(visitor.visit_loop_kind(kind)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety_mode)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_expr_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(assoc_item)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_ident(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_generic_param(visitor_item)?);
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value
                            .append(visitor.visit_generic_constraint(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                    visitor_reduce_value.append(visitor.visit_span(span)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_ty(visitor_item_1)?);
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    for visitor_item in variants {
                        visitor_reduce_value.append(visitor.visit_variant(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_trait_item(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_generics(generics)?;
                    visitor_reduce_value.append(visitor.visit_ty(self_ty)?);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_impl_item(visitor_item)?);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1)?);
                        };
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote)?;
                    visitor_reduce_value.append(visitor.visit_item_quote_origin(origin)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduceCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident)?;
                visitor_reduce_value.append(visitor.visit_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
}
pub mod map_cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapCf: HasSpan {
        type Error;
        fn visit_global_id(&mut self, v: &mut GlobalId) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &mut LocalId) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &mut IntSize) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_size(self, v)
        }
        fn visit_signedness(
            &mut self,
            v: &mut Signedness,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &mut IntKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(
            &mut self,
            v: &mut FloatKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &mut Literal) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &mut ResugaredItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &mut ResugaredExprKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &mut ResugaredPatKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &mut ResugaredTyKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &mut ResugaredImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &mut ResugaredTraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &mut Span) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_span(self, v)
        }
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &mut Region) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &mut Ty) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &mut TyKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(
            &mut self,
            v: &mut ErrorNode,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &mut Metadata) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &mut Guard) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &mut PatKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &mut Lhs) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &mut ImplExpr) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &mut ImplItem) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &mut Quote) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &mut LoopKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &mut ExprKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &mut Generics) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &mut Attribute) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &mut Param) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &mut Variant) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &mut ItemKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &mut Item) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size)?;
                    visitor.visit_signedness(signedness)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Span,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Ty,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item)?;
                    }
                    visitor.visit_ty(output)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner)?;
                    visitor.visit_region(region)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty)?;
                    visitor.visit_expr(length.deref_mut())?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(()),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(item)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_)?;
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref_mut())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref_mut())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat)?;
                visitor.visit_expr(body)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(()),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(()),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_spanned_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var)?;
                    visitor.visit_binding_mode(mode)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_pat(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref_mut())?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref_mut())?;
                    visitor.visit_ty(ty)?;
                    visitor.visit_global_id(field)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref_mut())?;
                    visitor.visit_ty(ty)?;
                    visitor.visit_expr(index)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref_mut())?;
                    visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_impl_ident(ident)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(item)?;
                    visitor.visit_impl_ident(ident)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_)?;
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_generics(generics)?;
                visitor.visit_impl_item_kind(kind)?;
                visitor.visit_global_id(ident)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0)?;
                            visitor.visit_impl_ident(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_trait_item_kind(kind)?;
                visitor.visit_generics(generics)?;
                visitor.visit_global_id(ident)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_trait_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(()),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind)?;
                    visitor.visit_global_id(item_ident)?;
                    visitor.visit_item_quote_origin_position(position)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::TyAlias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::MacroInvocation { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Trait { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Alias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Quote { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::HaxError { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::Replace { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => std::ops::ControlFlow::Continue(()),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_expr(iterator)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start)?;
                    visitor.visit_expr(end)?;
                    visitor.visit_local_id(var)?;
                    visitor.visit_ty(var_ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
                ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init)?;
                    visitor.visit_pat(body_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition)?;
                    visitor.visit_expr(then)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item)?;
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_expr(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs)?;
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_loop_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item)?;
                    }
                    visitor.visit_expr(body)?;
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_safety_kind(safety_mode)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(assoc_item)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident)?;
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item)?;
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind)?;
                    visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(()),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Param,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_ty(visitor_item_1)?;
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    visitor.visit_safety_kind(safety)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics)?;
                    visitor.visit_ty(self_ty)?;
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0)?;
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item)?;
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item)?;
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0)?;
                            visitor.visit_impl_ident(visitor_item_1)?;
                        };
                    }
                    visitor.visit_safety_kind(safety)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_global_id(item)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote)?;
                    visitor.visit_item_quote_origin(origin)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapCf + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident)?;
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
}
pub mod reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait ReduceCf<'lt>: HasSpan {
        type Error;
        type Out: Monoid;
        fn visit_global_id(
            &mut self,
            v: &'lt GlobalId,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_global_id(self, v)
        }
        fn visit_local_id(
            &mut self,
            v: &'lt LocalId,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_local_id(self, v)
        }
        fn visit_int_size(
            &mut self,
            v: &'lt IntSize,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_size(self, v)
        }
        fn visit_signedness(
            &mut self,
            v: &'lt Signedness,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_signedness(self, v)
        }
        fn visit_int_kind(
            &mut self,
            v: &'lt IntKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(
            &mut self,
            v: &'lt FloatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_float_kind(self, v)
        }
        fn visit_literal(
            &mut self,
            v: &'lt Literal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &'lt ResugaredItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &'lt ResugaredExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &'lt ResugaredPatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &'lt ResugaredTyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &'lt ResugaredImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &'lt ResugaredTraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &'lt Span) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_span(self, v)
        }
        fn visit_generic_value(
            &mut self,
            v: &'lt GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &'lt PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(
            &mut self,
            v: &'lt Region,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &'lt Ty) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(
            &mut self,
            v: &'lt TyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(
            &mut self,
            v: &'lt ErrorNode,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &'lt DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(
            &mut self,
            v: &'lt Metadata,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &'lt Expr) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &'lt Pat) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &'lt Arm) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &'lt Guard) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &'lt BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &'lt BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(
            &mut self,
            v: &'lt PatKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &'lt GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &'lt Lhs) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(
            &mut self,
            v: &'lt ImplExpr,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &'lt ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(
            &mut self,
            v: &'lt ImplItem,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &'lt ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &'lt TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &'lt TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &'lt QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &'lt Quote) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &'lt ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &'lt ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &'lt ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(
            &mut self,
            v: &'lt LoopKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &'lt ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &'lt LoopState,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(
            &mut self,
            v: &'lt ExprKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &'lt GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &'lt TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &'lt ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &'lt ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &'lt GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &'lt GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generic_param(self, v)
        }
        fn visit_generics(
            &mut self,
            v: &'lt Generics,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &'lt SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(
            &mut self,
            v: &'lt Attribute,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &'lt AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &'lt DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &'lt SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &'lt Param) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_param(self, v)
        }
        fn visit_variant(
            &mut self,
            v: &'lt Variant,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_variant(self, v)
        }
        fn visit_item_kind(
            &mut self,
            v: &'lt ItemKind,
        ) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &'lt Item) -> std::ops::ControlFlow<Self::Error, Self::Out> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size)?;
                    visitor_reduce_value.append(visitor.visit_signedness(signedness)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericValue::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref())?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner)?;
                    visitor_reduce_value.append(visitor.visit_region(region)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    visitor_reduce_value.append(visitor.visit_expr(length.deref())?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_dyn_trait_goal(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_ty_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ErrorNode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_)?;
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                visitor_reduce_value.append(visitor.visit_expr(body)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_spanned_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var)?;
                    visitor_reduce_value.append(visitor.visit_binding_mode(mode)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_pat_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref())?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref())?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    visitor_reduce_value.append(visitor.visit_global_id(field)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref())?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    visitor_reduce_value.append(visitor.visit_expr(index)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref())?;
                    visitor_reduce_value.append(visitor.visit_trait_goal(goal)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::LocalBound { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                visitor_reduce_value.append(visitor.visit_generics(generics)?);
                visitor_reduce_value.append(visitor.visit_impl_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_global_id(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_impl_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                visitor_reduce_value.append(visitor.visit_trait_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_generics(generics)?);
                visitor_reduce_value.append(visitor.visit_global_id(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_trait_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_quote_content(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item_ident)?);
                    visitor_reduce_value
                        .append(visitor.visit_item_quote_origin_position(position)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::TyAlias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::MacroInvocation { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Trait { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Impl { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Alias { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Use { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::Quote { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::HaxError { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::After { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ItemQuoteOriginPosition::Replace { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_expr(iterator)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start)?;
                    visitor_reduce_value.append(visitor.visit_expr(end)?);
                    visitor_reduce_value.append(visitor.visit_local_id(var)?);
                    visitor_reduce_value.append(visitor.visit_ty(var_ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                ControlFlowKind::BreakOrReturn { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init)?;
                    visitor_reduce_value.append(visitor.visit_pat(body_pat)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition)?;
                    visitor_reduce_value.append(visitor.visit_expr(then)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1)?);
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor_reduce_value.append(visitor.visit_arm(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs)?;
                    visitor_reduce_value.append(visitor.visit_expr(value)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value.append(visitor.visit_loop_kind(kind)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body)?;
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety_mode)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_expr_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Type { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_)?;
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                    visitor_reduce_value.append(visitor.visit_global_id(assoc_item)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_ident(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_generic_param(visitor_item)?);
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value
                            .append(visitor.visit_generic_constraint(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                    visitor_reduce_value.append(visitor.visit_span(span)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat)?;
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_ty(visitor_item_1)?);
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    visitor_reduce_value.append(visitor.visit_expr(body)?);
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item)?);
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    visitor_reduce_value.append(visitor.visit_ty(ty)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    for visitor_item in variants {
                        visitor_reduce_value.append(visitor.visit_variant(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_generics(generics)?);
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_trait_item(visitor_item)?);
                    }
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_generics(generics)?;
                    visitor_reduce_value.append(visitor.visit_ty(self_ty)?);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0)?);
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(visitor.visit_generic_value(visitor_item)?);
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_impl_item(visitor_item)?);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0)?);
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1)?);
                        };
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name)?;
                    visitor_reduce_value.append(visitor.visit_global_id(item)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote)?;
                    visitor_reduce_value.append(visitor.visit_item_quote_origin(origin)?);
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(visitor_reduce_value)
                }
                ItemKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(V::Out::identity())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: ReduceCf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident)?;
                visitor_reduce_value.append(visitor.visit_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        });
        result
    }
}
pub mod cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait Cf<'lt>: HasSpan {
        type Error;
        fn visit_global_id(&mut self, v: &'lt GlobalId) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &'lt LocalId) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &'lt IntSize) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_size(self, v)
        }
        fn visit_signedness(
            &mut self,
            v: &'lt Signedness,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &'lt IntKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(
            &mut self,
            v: &'lt FloatKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &'lt Literal) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(
            &mut self,
            v: &'lt ResugaredItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(
            &mut self,
            v: &'lt ResugaredExprKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(
            &mut self,
            v: &'lt ResugaredPatKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(
            &mut self,
            v: &'lt ResugaredTyKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(
            &mut self,
            v: &'lt ResugaredImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(
            &mut self,
            v: &'lt ResugaredTraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &'lt Span) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_span(self, v)
        }
        fn visit_generic_value(
            &mut self,
            v: &'lt GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &'lt PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &'lt Region) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &'lt Ty) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &'lt TyKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(
            &mut self,
            v: &'lt ErrorNode,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &'lt DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &'lt Metadata) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &'lt Expr) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &'lt Pat) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &'lt Arm) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &'lt Guard) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &'lt BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &'lt BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &'lt PatKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &'lt GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &'lt Lhs) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &'lt ImplExpr) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &'lt ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &'lt ImplItem) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &'lt ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &'lt TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &'lt TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &'lt QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &'lt Quote) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &'lt ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &'lt ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &'lt ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &'lt LoopKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &'lt ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &'lt LoopState,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &'lt ExprKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &'lt GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &'lt TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &'lt ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &'lt ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &'lt GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &'lt GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &'lt Generics) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &'lt SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &'lt Attribute) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &'lt AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &'lt DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &'lt SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &'lt Param) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &'lt Variant) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &'lt ItemKind) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &'lt Item) -> std::ops::ControlFlow<Self::Error, ()> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntSize::S8 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S16 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S32 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S64 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::S128 { .. } => std::ops::ControlFlow::Continue(()),
                IntSize::SSize { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Signedness::Signed { .. } => std::ops::ControlFlow::Continue(()),
                Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size)?;
                    visitor.visit_signedness(signedness)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(()),
                FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Literal::String { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Char { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Bool { .. } => std::ops::ControlFlow::Continue(()),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(()),
                PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Region { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref())?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item)?;
                    }
                    visitor.visit_ty(output)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner)?;
                    visitor.visit_region(region)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty)?;
                    visitor.visit_expr(length.deref())?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(()),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(item)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ErrorNode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_)?;
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat)?;
                visitor.visit_expr(body)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(()),
                BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(()),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                PatKind::Wild { .. } => std::ops::ControlFlow::Continue(()),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_spanned_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var)?;
                    visitor.visit_binding_mode(mode)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_pat(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref())?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref())?;
                    visitor.visit_ty(ty)?;
                    visitor.visit_global_id(field)?;
                    std::ops::ControlFlow::Continue(())
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref())?;
                    visitor.visit_ty(ty)?;
                    visitor.visit_expr(index)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref())?;
                    visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_impl_ident(ident)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(item)?;
                    visitor.visit_impl_ident(ident)?;
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_)?;
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(()),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_generics(generics)?;
                visitor.visit_impl_item_kind(kind)?;
                visitor.visit_global_id(ident)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty)?;
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0)?;
                            visitor.visit_impl_ident(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_trait_item_kind(kind)?;
                visitor.visit_generics(generics)?;
                visitor.visit_global_id(ident)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_trait_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(()),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind)?;
                    visitor.visit_global_id(item_ident)?;
                    visitor.visit_item_quote_origin_position(position)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::TyAlias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::MacroInvocation { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Trait { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Alias { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::Quote { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::HaxError { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginKind::NotImplementedYet { .. } => {
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(()),
                ItemQuoteOriginPosition::Replace { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => std::ops::ControlFlow::Continue(()),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_expr(iterator)?;
                    std::ops::ControlFlow::Continue(())
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start)?;
                    visitor.visit_expr(end)?;
                    visitor.visit_local_id(var)?;
                    visitor.visit_ty(var_ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
                ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init)?;
                    visitor.visit_pat(body_pat)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition)?;
                    visitor.visit_expr(then)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head)?;
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item)?;
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor)?;
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_expr(visitor_item_1)?;
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee)?;
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs)?;
                    visitor.visit_expr(rhs)?;
                    visitor.visit_expr(body)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs)?;
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_loop_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(()),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item)?;
                    }
                    visitor.visit_expr(body)?;
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body)?;
                    visitor.visit_safety_kind(safety_mode)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(()),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_)?;
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_)?;
                    visitor.visit_global_id(assoc_item)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident)?;
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item)?;
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
                SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind)?;
                    visitor.visit_span(span)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(()),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
                DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name)?;
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0)?;
                            visitor.visit_ty(visitor_item_1)?;
                            ();
                        };
                    }
                    std::ops::ControlFlow::Continue(())
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    visitor.visit_expr(body)?;
                    for visitor_item in params {
                        visitor.visit_param(visitor_item)?;
                    }
                    visitor.visit_safety_kind(safety)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    visitor.visit_ty(ty)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_generics(generics)?;
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item)?;
                    }
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics)?;
                    visitor.visit_ty(self_ty)?;
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0)?;
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item)?;
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item)?;
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0)?;
                            visitor.visit_impl_ident(visitor_item_1)?;
                        };
                    }
                    visitor.visit_safety_kind(safety)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name)?;
                    visitor.visit_global_id(item)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Use { .. } => std::ops::ControlFlow::Continue(()),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote)?;
                    visitor.visit_item_quote_origin(origin)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0)?;
                    std::ops::ControlFlow::Continue(())
                }
                ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Cf<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident)?;
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        });
        result
    }
}
pub mod map_reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait MapReduce: HasSpan {
        type Out: Monoid;
        fn visit_global_id(&mut self, v: &mut GlobalId) -> Self::Out {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &mut LocalId) -> Self::Out {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &mut IntSize) -> Self::Out {
            visit_int_size(self, v)
        }
        fn visit_signedness(&mut self, v: &mut Signedness) -> Self::Out {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &mut IntKind) -> Self::Out {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(&mut self, v: &mut FloatKind) -> Self::Out {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &mut Literal) -> Self::Out {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(&mut self, v: &mut ResugaredItemKind) -> Self::Out {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(&mut self, v: &mut ResugaredExprKind) -> Self::Out {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(&mut self, v: &mut ResugaredPatKind) -> Self::Out {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(&mut self, v: &mut ResugaredTyKind) -> Self::Out {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(&mut self, v: &mut ResugaredImplItemKind) -> Self::Out {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(&mut self, v: &mut ResugaredTraitItemKind) -> Self::Out {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &mut Span) -> Self::Out {
            visit_span(self, v)
        }
        fn visit_generic_value(&mut self, v: &mut GenericValue) -> Self::Out {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &mut PrimitiveTy) -> Self::Out {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &mut Region) -> Self::Out {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &mut Ty) -> Self::Out {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &mut TyKind) -> Self::Out {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(&mut self, v: &mut ErrorNode) -> Self::Out {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &mut DynTraitGoal) -> Self::Out {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &mut Metadata) -> Self::Out {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> Self::Out {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> Self::Out {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm) -> Self::Out {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &mut Guard) -> Self::Out {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &mut BorrowKind) -> Self::Out {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &mut BindingMode) -> Self::Out {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &mut PatKind) -> Self::Out {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &mut GuardKind) -> Self::Out {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &mut Lhs) -> Self::Out {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &mut ImplExpr) -> Self::Out {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &mut ImplExprKind) -> Self::Out {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &mut ImplItem) -> Self::Out {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &mut ImplItemKind) -> Self::Out {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &mut TraitItem) -> Self::Out {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &mut TraitItemKind) -> Self::Out {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &mut QuoteContent) -> Self::Out {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &mut Quote) -> Self::Out {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &mut ItemQuoteOrigin) -> Self::Out {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(&mut self, v: &mut ItemQuoteOriginKind) -> Self::Out {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
        ) -> Self::Out {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &mut LoopKind) -> Self::Out {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &mut ControlFlowKind) -> Self::Out {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &mut LoopState) -> Self::Out {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &mut ExprKind) -> Self::Out {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &mut GenericParamKind) -> Self::Out {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &mut TraitGoal) -> Self::Out {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &mut ImplIdent) -> Self::Out {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(&mut self, v: &mut ProjectionPredicate) -> Self::Out {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &mut GenericConstraint) -> Self::Out {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &mut GenericParam) -> Self::Out {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &mut Generics) -> Self::Out {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &mut SafetyKind) -> Self::Out {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &mut Attribute) -> Self::Out {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &mut AttributeKind) -> Self::Out {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &mut DocCommentKind) -> Self::Out {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &mut SpannedTy) -> Self::Out {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &mut Param) -> Self::Out {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &mut Variant) -> Self::Out {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &mut ItemKind) -> Self::Out {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &mut Item) -> Self::Out {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GlobalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LocalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntSize,
    ) -> V::Out {
        let result = {
            match v {
                IntSize::S8 { .. } => V::Out::identity(),
                IntSize::S16 { .. } => V::Out::identity(),
                IntSize::S32 { .. } => V::Out::identity(),
                IntSize::S64 { .. } => V::Out::identity(),
                IntSize::S128 { .. } => V::Out::identity(),
                IntSize::SSize { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Signedness,
    ) -> V::Out {
        let result = {
            match v {
                Signedness::Signed { .. } => V::Out::identity(),
                Signedness::Unsigned { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut IntKind,
    ) -> V::Out {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size);
                    visitor_reduce_value.append(visitor.visit_signedness(signedness));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut FloatKind,
    ) -> V::Out {
        let result = {
            match v {
                FloatKind::F16 { .. } => V::Out::identity(),
                FloatKind::F32 { .. } => V::Out::identity(),
                FloatKind::F64 { .. } => V::Out::identity(),
                FloatKind::F128 { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Literal,
    ) -> V::Out {
        let result = {
            match v {
                Literal::String { .. } => V::Out::identity(),
                Literal::Char { .. } => V::Out::identity(),
                Literal::Bool { .. } => V::Out::identity(),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind);
                    visitor_reduce_value
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(kind);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> V::Out {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Span) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> V::Out {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                GenericValue::Lifetime { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> V::Out {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => V::Out::identity(),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(anon_field_0);
                    visitor_reduce_value
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(anon_field_0);
                    visitor_reduce_value
                }
                PrimitiveTy::Char { .. } => V::Out::identity(),
                PrimitiveTy::Str { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Region,
    ) -> V::Out {
        let result = {
            match v {
                Region { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Ty) -> V::Out {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut());
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> V::Out {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output));
                    visitor_reduce_value
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner);
                    visitor_reduce_value.append(visitor.visit_region(region));
                    visitor_reduce_value
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    visitor_reduce_value.append(visitor.visit_expr(length.deref_mut()));
                    visitor_reduce_value
                }
                TyKind::RawPointer { .. } => V::Out::identity(),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_dyn_trait_goal(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_ty_kind(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ErrorNode,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> V::Out {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_);
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> V::Out {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Expr) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Pat) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Arm) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat);
                visitor_reduce_value.append(visitor.visit_expr(body));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Guard) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> V::Out {
        let result = {
            match v {
                BorrowKind::Shared { .. } => V::Out::identity(),
                BorrowKind::Unique { .. } => V::Out::identity(),
                BorrowKind::Mut { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> V::Out {
        let result = {
            match v {
                BindingMode::ByValue { .. } => V::Out::identity(),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> V::Out {
        let result = {
            match v {
                PatKind::Wild { .. } => V::Out::identity(),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_spanned_ty(ty));
                    visitor_reduce_value
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat);
                    visitor_reduce_value
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit);
                    visitor_reduce_value
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var);
                    visitor_reduce_value.append(visitor.visit_binding_mode(mode));
                    visitor_reduce_value
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_pat_kind(anon_field_0);
                    visitor_reduce_value
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> V::Out {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Lhs) -> V::Out {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut());
                    visitor_reduce_value
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut());
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value.append(visitor.visit_global_id(field));
                    visitor_reduce_value
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref_mut());
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value.append(visitor.visit_expr(index));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> V::Out {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut());
                    visitor_reduce_value.append(visitor.visit_trait_goal(goal));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> V::Out {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => V::Out::identity(),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                    visitor_reduce_value
                }
                ImplExprKind::LocalBound { .. } => V::Out::identity(),
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident));
                    visitor_reduce_value
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident));
                    visitor_reduce_value
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ImplExprKind::Dyn { .. } => V::Out::identity(),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta);
                visitor_reduce_value.append(visitor.visit_generics(generics));
                visitor_reduce_value.append(visitor.visit_impl_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_global_id(ident));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> V::Out {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_impl_item_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta);
                visitor_reduce_value.append(visitor.visit_trait_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_generics(generics));
                visitor_reduce_value.append(visitor.visit_global_id(ident));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> V::Out {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item));
                    }
                    visitor_reduce_value
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_trait_item_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> V::Out {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => V::Out::identity(),
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Quote) -> V::Out {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_quote_content(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind);
                    visitor_reduce_value.append(visitor.visit_global_id(item_ident));
                    visitor_reduce_value.append(visitor.visit_item_quote_origin_position(position));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => V::Out::identity(),
                ItemQuoteOriginKind::TyAlias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Type { .. } => V::Out::identity(),
                ItemQuoteOriginKind::MacroInvocation { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Trait { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Impl { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Alias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Use { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Quote { .. } => V::Out::identity(),
                ItemQuoteOriginKind::HaxError { .. } => V::Out::identity(),
                ItemQuoteOriginKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::After { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::Replace { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> V::Out {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => V::Out::identity(),
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_expr(iterator));
                    visitor_reduce_value
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start);
                    visitor_reduce_value.append(visitor.visit_expr(end));
                    visitor_reduce_value.append(visitor.visit_local_id(var));
                    visitor_reduce_value.append(visitor.visit_ty(var_ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> V::Out {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => V::Out::identity(),
                ControlFlowKind::BreakOrReturn { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> V::Out {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init);
                    visitor_reduce_value.append(visitor.visit_pat(body_pat));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> V::Out {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value.append(visitor.visit_expr(then));
                    visitor_reduce_value
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor_reduce_value.append(visitor.visit_arm(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(value));
                    visitor_reduce_value
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value.append(visitor.visit_loop_kind(kind));
                    visitor_reduce_value
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Continue { .. } => V::Out::identity(),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety_mode));
                    visitor_reduce_value
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents);
                    visitor_reduce_value
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_expr_kind(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> V::Out {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => V::Out::identity(),
                GenericParamKind::Type { .. } => V::Out::identity(),
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> V::Out {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> V::Out {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(goal);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> V::Out {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(assoc_item));
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> V::Out {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => V::Out::identity(),
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_ident(anon_field_0);
                    visitor_reduce_value
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> V::Out {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_generic_param(visitor_item));
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value.append(visitor.visit_generic_constraint(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> V::Out {
        let result = {
            match v {
                SafetyKind::Safe { .. } => V::Out::identity(),
                SafetyKind::Unsafe { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> V::Out {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_attribute_kind(kind);
                    visitor_reduce_value.append(visitor.visit_span(span));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> V::Out {
        let result = {
            match v {
                AttributeKind::Tool { .. } => V::Out::identity(),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> V::Out {
        let result = {
            match v {
                DocCommentKind::Line { .. } => V::Out::identity(),
                DocCommentKind::Block { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> V::Out {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Param) -> V::Out {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> V::Out {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_ty(visitor_item_1));
                            ();
                        };
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduce + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> V::Out {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety));
                    visitor_reduce_value
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    for visitor_item in variants {
                        visitor_reduce_value.append(visitor.visit_variant(visitor_item));
                    }
                    visitor_reduce_value
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_trait_item(visitor_item));
                    }
                    visitor_reduce_value
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_generics(generics);
                    visitor_reduce_value.append(visitor.visit_ty(self_ty));
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_impl_item(visitor_item));
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1));
                        };
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety));
                    visitor_reduce_value
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value
                }
                ItemKind::Use { .. } => V::Out::identity(),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote);
                    visitor_reduce_value.append(visitor.visit_item_quote_origin(origin));
                    visitor_reduce_value
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0);
                    visitor_reduce_value
                }
                ItemKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduce + ?Sized + HasSpan>(visitor: &mut V, v: &mut Item) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident);
                visitor_reduce_value.append(visitor.visit_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
}
pub mod map {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait Map: HasSpan {
        fn visit_global_id(&mut self, v: &mut GlobalId) -> () {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &mut LocalId) -> () {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &mut IntSize) -> () {
            visit_int_size(self, v)
        }
        fn visit_signedness(&mut self, v: &mut Signedness) -> () {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &mut IntKind) -> () {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(&mut self, v: &mut FloatKind) -> () {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &mut Literal) -> () {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(&mut self, v: &mut ResugaredItemKind) -> () {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(&mut self, v: &mut ResugaredExprKind) -> () {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(&mut self, v: &mut ResugaredPatKind) -> () {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(&mut self, v: &mut ResugaredTyKind) -> () {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(&mut self, v: &mut ResugaredImplItemKind) -> () {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(&mut self, v: &mut ResugaredTraitItemKind) -> () {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &mut Span) -> () {
            visit_span(self, v)
        }
        fn visit_generic_value(&mut self, v: &mut GenericValue) -> () {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &mut PrimitiveTy) -> () {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &mut Region) -> () {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &mut Ty) -> () {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &mut TyKind) -> () {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(&mut self, v: &mut ErrorNode) -> () {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &mut DynTraitGoal) -> () {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &mut Metadata) -> () {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> () {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> () {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm) -> () {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &mut Guard) -> () {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &mut BorrowKind) -> () {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &mut BindingMode) -> () {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &mut PatKind) -> () {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &mut GuardKind) -> () {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &mut Lhs) -> () {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &mut ImplExpr) -> () {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &mut ImplExprKind) -> () {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &mut ImplItem) -> () {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &mut ImplItemKind) -> () {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &mut TraitItem) -> () {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &mut TraitItemKind) -> () {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &mut QuoteContent) -> () {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &mut Quote) -> () {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &mut ItemQuoteOrigin) -> () {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(&mut self, v: &mut ItemQuoteOriginKind) -> () {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(&mut self, v: &mut ItemQuoteOriginPosition) -> () {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &mut LoopKind) -> () {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &mut ControlFlowKind) -> () {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &mut LoopState) -> () {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &mut ExprKind) -> () {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &mut GenericParamKind) -> () {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &mut TraitGoal) -> () {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &mut ImplIdent) -> () {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(&mut self, v: &mut ProjectionPredicate) -> () {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &mut GenericConstraint) -> () {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &mut GenericParam) -> () {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &mut Generics) -> () {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &mut SafetyKind) -> () {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &mut Attribute) -> () {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &mut AttributeKind) -> () {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &mut DocCommentKind) -> () {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &mut SpannedTy) -> () {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &mut Param) -> () {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &mut Variant) -> () {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &mut ItemKind) -> () {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &mut Item) -> () {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut GlobalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut LocalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut IntSize) -> () {
        let result = {
            match v {
                IntSize::S8 { .. } => (),
                IntSize::S16 { .. } => (),
                IntSize::S32 { .. } => (),
                IntSize::S64 { .. } => (),
                IntSize::S128 { .. } => (),
                IntSize::SSize { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Signedness) -> () {
        let result = {
            match v {
                Signedness::Signed { .. } => (),
                Signedness::Unsigned { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut IntKind) -> () {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size);
                    visitor.visit_signedness(signedness);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut FloatKind) -> () {
        let result = {
            match v {
                FloatKind::F16 { .. } => (),
                FloatKind::F32 { .. } => (),
                FloatKind::F64 { .. } => (),
                FloatKind::F128 { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Literal) -> () {
        let result = {
            match v {
                Literal::String { .. } => (),
                Literal::Char { .. } => (),
                Literal::Bool { .. } => (),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind);
                    ()
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> () {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Span) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> () {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                GenericValue::Lifetime { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> () {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => (),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0);
                    ()
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0);
                    ()
                }
                PrimitiveTy::Char { .. } => (),
                PrimitiveTy::Str { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Region) -> () {
        let result = {
            match v {
                Region { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Ty) -> () {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref_mut());
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut TyKind) -> () {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0);
                    ()
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item);
                    }
                    ()
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item);
                    }
                    visitor.visit_ty(output);
                    ()
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner);
                    visitor.visit_region(region);
                    ()
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0);
                    ()
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty);
                    visitor.visit_expr(length.deref_mut());
                    ()
                }
                TyKind::RawPointer { .. } => (),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(item);
                    ()
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0);
                    ()
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item);
                    }
                    ()
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0);
                    ()
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ErrorNode) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> () {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_);
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Metadata) -> () {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Expr) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref_mut());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Pat) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref_mut());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Arm) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat);
                visitor.visit_expr(body);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Guard) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut BorrowKind) -> () {
        let result = {
            match v {
                BorrowKind::Shared { .. } => (),
                BorrowKind::Unique { .. } => (),
                BorrowKind::Mut { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> () {
        let result = {
            match v {
                BindingMode::ByValue { .. } => (),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut PatKind) -> () {
        let result = {
            match v {
                PatKind::Wild { .. } => (),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat);
                    visitor.visit_spanned_ty(ty);
                    ()
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat);
                    ()
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit);
                    ()
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var);
                    visitor.visit_binding_mode(mode);
                    ()
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_pat(visitor_item_1);
                        };
                    }
                    ()
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0);
                    ()
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut GuardKind) -> () {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Lhs) -> () {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var);
                    visitor.visit_ty(ty);
                    ()
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref_mut());
                    ()
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref_mut());
                    visitor.visit_ty(ty);
                    visitor.visit_global_id(field);
                    ()
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref_mut());
                    visitor.visit_ty(ty);
                    visitor.visit_expr(index);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ImplExpr) -> () {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref_mut());
                    visitor.visit_trait_goal(goal);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> () {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => (),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0);
                    ()
                }
                ImplExprKind::LocalBound { .. } => (),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_impl_ident(ident);
                    ()
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(item);
                    visitor.visit_impl_ident(ident);
                    ()
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_);
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item);
                    }
                    ()
                }
                ImplExprKind::Dyn { .. } => (),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ImplItem) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta);
                visitor.visit_generics(generics);
                visitor.visit_impl_item_kind(kind);
                visitor.visit_global_id(ident);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> () {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0);
                            visitor.visit_impl_ident(visitor_item_1);
                        };
                    }
                    ()
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    ()
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut TraitItem) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta);
                visitor.visit_trait_item_kind(kind);
                visitor.visit_generics(generics);
                visitor.visit_global_id(ident);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> () {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item);
                    }
                    ()
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    visitor.visit_expr(body);
                    ()
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_trait_item_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> () {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => (),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0);
                    ()
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Quote) -> () {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind);
                    visitor.visit_global_id(item_ident);
                    visitor.visit_item_quote_origin_position(position);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => (),
                ItemQuoteOriginKind::TyAlias { .. } => (),
                ItemQuoteOriginKind::Type { .. } => (),
                ItemQuoteOriginKind::MacroInvocation { .. } => (),
                ItemQuoteOriginKind::Trait { .. } => (),
                ItemQuoteOriginKind::Impl { .. } => (),
                ItemQuoteOriginKind::Alias { .. } => (),
                ItemQuoteOriginKind::Use { .. } => (),
                ItemQuoteOriginKind::Quote { .. } => (),
                ItemQuoteOriginKind::HaxError { .. } => (),
                ItemQuoteOriginKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => (),
                ItemQuoteOriginPosition::After { .. } => (),
                ItemQuoteOriginPosition::Replace { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut LoopKind) -> () {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => (),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition);
                    ()
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat);
                    visitor.visit_expr(iterator);
                    ()
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start);
                    visitor.visit_expr(end);
                    visitor.visit_local_id(var);
                    visitor.visit_ty(var_ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> () {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => (),
                ControlFlowKind::BreakOrReturn { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut LoopState) -> () {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init);
                    visitor.visit_pat(body_pat);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ExprKind) -> () {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition);
                    visitor.visit_expr(then);
                    ()
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item);
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0);
                    ()
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_expr(visitor_item_1);
                        };
                    }
                    ()
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item);
                    }
                    ()
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    visitor.visit_expr(body);
                    ()
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0);
                    ()
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0);
                    ()
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e);
                    visitor.visit_ty(ty);
                    ()
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs);
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body);
                    visitor.visit_loop_kind(kind);
                    ()
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Continue { .. } => (),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item);
                    }
                    visitor.visit_expr(body);
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body);
                    visitor.visit_safety_kind(safety_mode);
                    ()
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents);
                    ()
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0);
                    ()
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> () {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => (),
                GenericParamKind::Type { .. } => (),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut TraitGoal) -> () {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ImplIdent) -> () {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> () {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(assoc_item);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> () {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => (),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0);
                    ()
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident);
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Generics) -> () {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item);
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut SafetyKind) -> () {
        let result = {
            match v {
                SafetyKind::Safe { .. } => (),
                SafetyKind::Unsafe { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Attribute) -> () {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind);
                    visitor.visit_span(span);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> () {
        let result = {
            match v {
                AttributeKind::Tool { .. } => (),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: Map + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> () {
        let result = {
            match v {
                DocCommentKind::Line { .. } => (),
                DocCommentKind::Block { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut SpannedTy) -> () {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Param) -> () {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Variant) -> () {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_ty(visitor_item_1);
                            ();
                        };
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut ItemKind) -> () {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    visitor.visit_safety_kind(safety);
                    ()
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    visitor.visit_ty(ty);
                    ()
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item);
                    }
                    ()
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item);
                    }
                    ()
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics);
                    visitor.visit_ty(self_ty);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0);
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item);
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0);
                            visitor.visit_impl_ident(visitor_item_1);
                        };
                    }
                    visitor.visit_safety_kind(safety);
                    ()
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name);
                    visitor.visit_global_id(item);
                    ()
                }
                ItemKind::Use { .. } => (),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote);
                    visitor.visit_item_quote_origin(origin);
                    ()
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0);
                    ()
                }
                ItemKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<V: Map + ?Sized + HasSpan>(visitor: &mut V, v: &mut Item) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident);
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
}
pub mod reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait Reduce<'lt>: HasSpan {
        type Out: Monoid;
        fn visit_global_id(&mut self, v: &'lt GlobalId) -> Self::Out {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &'lt LocalId) -> Self::Out {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &'lt IntSize) -> Self::Out {
            visit_int_size(self, v)
        }
        fn visit_signedness(&mut self, v: &'lt Signedness) -> Self::Out {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &'lt IntKind) -> Self::Out {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(&mut self, v: &'lt FloatKind) -> Self::Out {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &'lt Literal) -> Self::Out {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(&mut self, v: &'lt ResugaredItemKind) -> Self::Out {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(&mut self, v: &'lt ResugaredExprKind) -> Self::Out {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(&mut self, v: &'lt ResugaredPatKind) -> Self::Out {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(&mut self, v: &'lt ResugaredTyKind) -> Self::Out {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(&mut self, v: &'lt ResugaredImplItemKind) -> Self::Out {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(&mut self, v: &'lt ResugaredTraitItemKind) -> Self::Out {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &'lt Span) -> Self::Out {
            visit_span(self, v)
        }
        fn visit_generic_value(&mut self, v: &'lt GenericValue) -> Self::Out {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &'lt PrimitiveTy) -> Self::Out {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &'lt Region) -> Self::Out {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &'lt Ty) -> Self::Out {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &'lt TyKind) -> Self::Out {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(&mut self, v: &'lt ErrorNode) -> Self::Out {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &'lt DynTraitGoal) -> Self::Out {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &'lt Metadata) -> Self::Out {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &'lt Expr) -> Self::Out {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &'lt Pat) -> Self::Out {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &'lt Arm) -> Self::Out {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &'lt Guard) -> Self::Out {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &'lt BorrowKind) -> Self::Out {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &'lt BindingMode) -> Self::Out {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &'lt PatKind) -> Self::Out {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &'lt GuardKind) -> Self::Out {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &'lt Lhs) -> Self::Out {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &'lt ImplExpr) -> Self::Out {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &'lt ImplExprKind) -> Self::Out {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &'lt ImplItem) -> Self::Out {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &'lt ImplItemKind) -> Self::Out {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &'lt TraitItem) -> Self::Out {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &'lt TraitItemKind) -> Self::Out {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &'lt QuoteContent) -> Self::Out {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &'lt Quote) -> Self::Out {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &'lt ItemQuoteOrigin) -> Self::Out {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(&mut self, v: &'lt ItemQuoteOriginKind) -> Self::Out {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &'lt ItemQuoteOriginPosition,
        ) -> Self::Out {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &'lt LoopKind) -> Self::Out {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &'lt ControlFlowKind) -> Self::Out {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &'lt LoopState) -> Self::Out {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &'lt ExprKind) -> Self::Out {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &'lt GenericParamKind) -> Self::Out {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &'lt TraitGoal) -> Self::Out {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &'lt ImplIdent) -> Self::Out {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(&mut self, v: &'lt ProjectionPredicate) -> Self::Out {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &'lt GenericConstraint) -> Self::Out {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &'lt GenericParam) -> Self::Out {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &'lt Generics) -> Self::Out {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &'lt SafetyKind) -> Self::Out {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &'lt Attribute) -> Self::Out {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &'lt AttributeKind) -> Self::Out {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &'lt DocCommentKind) -> Self::Out {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &'lt SpannedTy) -> Self::Out {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &'lt Param) -> Self::Out {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &'lt Variant) -> Self::Out {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &'lt ItemKind) -> Self::Out {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &'lt Item) -> Self::Out {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> V::Out {
        let result = {
            match v {
                IntSize::S8 { .. } => V::Out::identity(),
                IntSize::S16 { .. } => V::Out::identity(),
                IntSize::S32 { .. } => V::Out::identity(),
                IntSize::S64 { .. } => V::Out::identity(),
                IntSize::S128 { .. } => V::Out::identity(),
                IntSize::SSize { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> V::Out {
        let result = {
            match v {
                Signedness::Signed { .. } => V::Out::identity(),
                Signedness::Unsigned { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> V::Out {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_size(size);
                    visitor_reduce_value.append(visitor.visit_signedness(signedness));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> V::Out {
        let result = {
            match v {
                FloatKind::F16 { .. } => V::Out::identity(),
                FloatKind::F32 { .. } => V::Out::identity(),
                FloatKind::F64 { .. } => V::Out::identity(),
                FloatKind::F128 { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> V::Out {
        let result = {
            match v {
                Literal::String { .. } => V::Out::identity(),
                Literal::Char { .. } => V::Out::identity(),
                Literal::Bool { .. } => V::Out::identity(),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(kind);
                    visitor_reduce_value
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(kind);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> V::Out {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> V::Out {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> V::Out {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                GenericValue::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                GenericValue::Lifetime { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> V::Out {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => V::Out::identity(),
                PrimitiveTy::Int(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_int_kind(anon_field_0);
                    visitor_reduce_value
                }
                PrimitiveTy::Float(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_float_kind(anon_field_0);
                    visitor_reduce_value
                }
                PrimitiveTy::Char { .. } => V::Out::identity(),
                PrimitiveTy::Str { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> V::Out {
        let result = {
            match v {
                Region { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(visitor: &mut V, v: &'lt Ty) -> V::Out {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref());
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> V::Out {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::App { head, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(head);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::Arrow { inputs, output } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in inputs {
                        visitor_reduce_value.append(visitor.visit_ty(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_ty(output));
                    visitor_reduce_value
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(inner);
                    visitor_reduce_value.append(visitor.visit_region(region));
                    visitor_reduce_value
                }
                TyKind::Param(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Slice(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Array { ty, length } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    visitor_reduce_value.append(visitor.visit_expr(length.deref()));
                    visitor_reduce_value
                }
                TyKind::RawPointer { .. } => V::Out::identity(),
                TyKind::AssociatedType { impl_, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value
                }
                TyKind::Opaque(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Dyn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_dyn_trait_goal(visitor_item));
                    }
                    visitor_reduce_value
                }
                TyKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_ty_kind(anon_field_0);
                    visitor_reduce_value
                }
                TyKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ErrorNode,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> V::Out {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_);
                    for visitor_item in non_self_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> V::Out {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(pat);
                visitor_reduce_value.append(visitor.visit_expr(body));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> V::Out {
        let result = {
            match v {
                BorrowKind::Shared { .. } => V::Out::identity(),
                BorrowKind::Unique { .. } => V::Out::identity(),
                BorrowKind::Mut { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> V::Out {
        let result = {
            match v {
                BindingMode::ByValue { .. } => V::Out::identity(),
                BindingMode::ByRef(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> V::Out {
        let result = {
            match v {
                PatKind::Wild { .. } => V::Out::identity(),
                PatKind::Ascription { pat, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_spanned_ty(ty));
                    visitor_reduce_value
                }
                PatKind::Or { sub_pats } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in sub_pats {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Array { args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value
                }
                PatKind::Deref { sub_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(sub_pat);
                    visitor_reduce_value
                }
                PatKind::Constant { lit } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(lit);
                    visitor_reduce_value
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var);
                    visitor_reduce_value.append(visitor.visit_binding_mode(mode));
                    visitor_reduce_value
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_pat(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                PatKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_pat_kind(anon_field_0);
                    visitor_reduce_value
                }
                PatKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> V::Out {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> V::Out {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(var);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0.deref());
                    visitor_reduce_value
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref());
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value.append(visitor.visit_global_id(field));
                    visitor_reduce_value
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(e.deref());
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value.append(visitor.visit_expr(index));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> V::Out {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref());
                    visitor_reduce_value.append(visitor.visit_trait_goal(goal));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> V::Out {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => V::Out::identity(),
                ImplExprKind::Concrete(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                    visitor_reduce_value
                }
                ImplExprKind::LocalBound { .. } => V::Out::identity(),
                ImplExprKind::Parent { impl_, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident));
                    visitor_reduce_value
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value.append(visitor.visit_impl_ident(ident));
                    visitor_reduce_value
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ImplExprKind::Dyn { .. } => V::Out::identity(),
                ImplExprKind::Builtin(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta);
                visitor_reduce_value.append(visitor.visit_generics(generics));
                visitor_reduce_value.append(visitor.visit_impl_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_global_id(ident));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> V::Out {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Fn { body, params } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_impl_item_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_metadata(meta);
                visitor_reduce_value.append(visitor.visit_trait_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_generics(generics));
                visitor_reduce_value.append(visitor.visit_global_id(ident));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> V::Out {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item));
                    }
                    visitor_reduce_value
                }
                TraitItemKind::Fn(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
                TraitItemKind::Default { params, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_trait_item_kind(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> V::Out {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => V::Out::identity(),
                QuoteContent::Expr(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Pattern(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(anon_field_0);
                    visitor_reduce_value
                }
                QuoteContent::Ty(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> V::Out {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_quote_content(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind);
                    visitor_reduce_value.append(visitor.visit_global_id(item_ident));
                    visitor_reduce_value.append(visitor.visit_item_quote_origin_position(position));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => V::Out::identity(),
                ItemQuoteOriginKind::TyAlias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Type { .. } => V::Out::identity(),
                ItemQuoteOriginKind::MacroInvocation { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Trait { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Impl { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Alias { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Use { .. } => V::Out::identity(),
                ItemQuoteOriginKind::Quote { .. } => V::Out::identity(),
                ItemQuoteOriginKind::HaxError { .. } => V::Out::identity(),
                ItemQuoteOriginKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> V::Out {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::After { .. } => V::Out::identity(),
                ItemQuoteOriginPosition::Replace { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> V::Out {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => V::Out::identity(),
                LoopKind::WhileLoop { condition } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value
                }
                LoopKind::ForLoop { pat, iterator } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_expr(iterator));
                    visitor_reduce_value
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(start);
                    visitor_reduce_value.append(visitor.visit_expr(end));
                    visitor_reduce_value.append(visitor.visit_local_id(var));
                    visitor_reduce_value.append(visitor.visit_ty(var_ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> V::Out {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => V::Out::identity(),
                ControlFlowKind::BreakOrReturn { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> V::Out {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(init);
                    visitor_reduce_value.append(visitor.visit_pat(body_pat));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> V::Out {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(condition);
                    visitor_reduce_value.append(visitor.visit_expr(then));
                    visitor_reduce_value
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    for visitor_item in generic_args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    for visitor_item in bounds_impls {
                        visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Literal(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_literal(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Array(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_expr(visitor_item_1));
                        };
                    }
                    visitor_reduce_value
                }
                ExprKind::Match { scrutinee, arms } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor_reduce_value.append(visitor.visit_arm(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Tuple(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in anon_field_0 {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Borrow { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::AddressOf { mutable, inner } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(inner);
                    visitor_reduce_value
                }
                ExprKind::Deref(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Let { lhs, rhs, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(rhs));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    visitor_reduce_value
                }
                ExprKind::GlobalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::LocalId(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_local_id(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Ascription { e, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(e);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                ExprKind::Assign { lhs, value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_lhs(lhs);
                    visitor_reduce_value.append(visitor.visit_expr(value));
                    visitor_reduce_value
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value.append(visitor.visit_loop_kind(kind));
                    visitor_reduce_value
                }
                ExprKind::Break { value, label } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Return { value } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(value);
                    visitor_reduce_value
                }
                ExprKind::Continue { .. } => V::Out::identity(),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_pat(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in captures {
                        visitor_reduce_value.append(visitor.visit_expr(visitor_item));
                    }
                    visitor_reduce_value
                }
                ExprKind::Block { body, safety_mode } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_expr(body);
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety_mode));
                    visitor_reduce_value
                }
                ExprKind::Quote { contents } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(contents);
                    visitor_reduce_value
                }
                ExprKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_expr_kind(anon_field_0);
                    visitor_reduce_value
                }
                ExprKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> V::Out {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => V::Out::identity(),
                GenericParamKind::Type { .. } => V::Out::identity(),
                GenericParamKind::Const { ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_ty(ty);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> V::Out {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(trait_);
                    for visitor_item in args {
                        visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> V::Out {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_trait_goal(goal);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> V::Out {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_expr(impl_);
                    visitor_reduce_value.append(visitor.visit_global_id(assoc_item));
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> V::Out {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => V::Out::identity(),
                GenericConstraint::Type(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_impl_ident(anon_field_0);
                    visitor_reduce_value
                }
                GenericConstraint::Projection(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind));
                visitor_reduce_value
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> V::Out {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = V::Out::identity();
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_generic_param(visitor_item));
                    }
                    for visitor_item in constraints {
                        visitor_reduce_value.append(visitor.visit_generic_constraint(visitor_item));
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> V::Out {
        let result = {
            match v {
                SafetyKind::Safe { .. } => V::Out::identity(),
                SafetyKind::Unsafe { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> V::Out {
        let result = {
            match v {
                Attribute { kind, span } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_attribute_kind(kind);
                    visitor_reduce_value.append(visitor.visit_span(span));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> V::Out {
        let result = {
            match v {
                AttributeKind::Tool { .. } => V::Out::identity(),
                AttributeKind::DocComment { kind, body } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> V::Out {
        let result = {
            match v {
                DocCommentKind::Line { .. } => V::Out::identity(),
                DocCommentKind::Block { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> V::Out {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_span(span);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> V::Out {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_pat(pat);
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> V::Out {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_ty(visitor_item_1));
                            ();
                        };
                    }
                    visitor_reduce_value
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> V::Out {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    visitor_reduce_value.append(visitor.visit_expr(body));
                    for visitor_item in params {
                        visitor_reduce_value.append(visitor.visit_param(visitor_item));
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety));
                    visitor_reduce_value
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    visitor_reduce_value.append(visitor.visit_ty(ty));
                    visitor_reduce_value
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    for visitor_item in variants {
                        visitor_reduce_value.append(visitor.visit_variant(visitor_item));
                    }
                    visitor_reduce_value
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_generics(generics));
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_trait_item(visitor_item));
                    }
                    visitor_reduce_value
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_generics(generics);
                    visitor_reduce_value.append(visitor.visit_ty(self_ty));
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor_reduce_value.append(visitor.visit_global_id(visitor_item_0));
                        for visitor_item in visitor_item_1 {
                            visitor_reduce_value.append(visitor.visit_generic_value(visitor_item));
                        }
                    };
                    for visitor_item in items {
                        visitor_reduce_value.append(visitor.visit_impl_item(visitor_item));
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor_reduce_value.append(visitor.visit_impl_expr(visitor_item_0));
                            visitor_reduce_value.append(visitor.visit_impl_ident(visitor_item_1));
                        };
                    }
                    visitor_reduce_value.append(visitor.visit_safety_kind(safety));
                    visitor_reduce_value
                }
                ItemKind::Alias { name, item } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_global_id(name);
                    visitor_reduce_value.append(visitor.visit_global_id(item));
                    visitor_reduce_value
                }
                ItemKind::Use { .. } => V::Out::identity(),
                ItemKind::Quote { quote, origin } => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_quote(quote);
                    visitor_reduce_value.append(visitor.visit_item_quote_origin(origin));
                    visitor_reduce_value
                }
                ItemKind::Error(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_error_node(anon_field_0);
                    visitor_reduce_value
                }
                ItemKind::Resugared(anon_field_0) => {
                    let mut visitor_reduce_value: V::Out;
                    visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0);
                    visitor_reduce_value
                }
                ItemKind::NotImplementedYet { .. } => V::Out::identity(),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Reduce<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> V::Out {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident);
                visitor_reduce_value.append(visitor.visit_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        });
        result
    }
}
pub mod vanilla {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait Vanilla<'lt>: HasSpan {
        fn visit_global_id(&mut self, v: &'lt GlobalId) -> () {
            visit_global_id(self, v)
        }
        fn visit_local_id(&mut self, v: &'lt LocalId) -> () {
            visit_local_id(self, v)
        }
        fn visit_int_size(&mut self, v: &'lt IntSize) -> () {
            visit_int_size(self, v)
        }
        fn visit_signedness(&mut self, v: &'lt Signedness) -> () {
            visit_signedness(self, v)
        }
        fn visit_int_kind(&mut self, v: &'lt IntKind) -> () {
            visit_int_kind(self, v)
        }
        fn visit_float_kind(&mut self, v: &'lt FloatKind) -> () {
            visit_float_kind(self, v)
        }
        fn visit_literal(&mut self, v: &'lt Literal) -> () {
            visit_literal(self, v)
        }
        fn visit_resugared_item_kind(&mut self, v: &'lt ResugaredItemKind) -> () {
            visit_resugared_item_kind(self, v)
        }
        fn visit_resugared_expr_kind(&mut self, v: &'lt ResugaredExprKind) -> () {
            visit_resugared_expr_kind(self, v)
        }
        fn visit_resugared_pat_kind(&mut self, v: &'lt ResugaredPatKind) -> () {
            visit_resugared_pat_kind(self, v)
        }
        fn visit_resugared_ty_kind(&mut self, v: &'lt ResugaredTyKind) -> () {
            visit_resugared_ty_kind(self, v)
        }
        fn visit_resugared_impl_item_kind(&mut self, v: &'lt ResugaredImplItemKind) -> () {
            visit_resugared_impl_item_kind(self, v)
        }
        fn visit_resugared_trait_item_kind(&mut self, v: &'lt ResugaredTraitItemKind) -> () {
            visit_resugared_trait_item_kind(self, v)
        }
        fn visit_span(&mut self, v: &'lt Span) -> () {
            visit_span(self, v)
        }
        fn visit_generic_value(&mut self, v: &'lt GenericValue) -> () {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &'lt PrimitiveTy) -> () {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &'lt Region) -> () {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &'lt Ty) -> () {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &'lt TyKind) -> () {
            visit_ty_kind(self, v)
        }
        fn visit_error_node(&mut self, v: &'lt ErrorNode) -> () {
            visit_error_node(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &'lt DynTraitGoal) -> () {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &'lt Metadata) -> () {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &'lt Expr) -> () {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &'lt Pat) -> () {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &'lt Arm) -> () {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &'lt Guard) -> () {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &'lt BorrowKind) -> () {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &'lt BindingMode) -> () {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &'lt PatKind) -> () {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &'lt GuardKind) -> () {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &'lt Lhs) -> () {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &'lt ImplExpr) -> () {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &'lt ImplExprKind) -> () {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &'lt ImplItem) -> () {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &'lt ImplItemKind) -> () {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &'lt TraitItem) -> () {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &'lt TraitItemKind) -> () {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &'lt QuoteContent) -> () {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &'lt Quote) -> () {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &'lt ItemQuoteOrigin) -> () {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(&mut self, v: &'lt ItemQuoteOriginKind) -> () {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(&mut self, v: &'lt ItemQuoteOriginPosition) -> () {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &'lt LoopKind) -> () {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &'lt ControlFlowKind) -> () {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &'lt LoopState) -> () {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &'lt ExprKind) -> () {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &'lt GenericParamKind) -> () {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &'lt TraitGoal) -> () {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &'lt ImplIdent) -> () {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(&mut self, v: &'lt ProjectionPredicate) -> () {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &'lt GenericConstraint) -> () {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &'lt GenericParam) -> () {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &'lt Generics) -> () {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &'lt SafetyKind) -> () {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &'lt Attribute) -> () {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &'lt AttributeKind) -> () {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &'lt DocCommentKind) -> () {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &'lt SpannedTy) -> () {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &'lt Param) -> () {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &'lt Variant) -> () {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &'lt ItemKind) -> () {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &'lt Item) -> () {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_global_id<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> () {
        let result = {
            match v {
                IntSize::S8 { .. } => (),
                IntSize::S16 { .. } => (),
                IntSize::S32 { .. } => (),
                IntSize::S64 { .. } => (),
                IntSize::S128 { .. } => (),
                IntSize::SSize { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> () {
        let result = {
            match v {
                Signedness::Signed { .. } => (),
                Signedness::Unsigned { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> () {
        let result = {
            match v {
                IntKind { size, signedness } => {
                    visitor.visit_int_size(size);
                    visitor.visit_signedness(signedness);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> () {
        let result = {
            match v {
                FloatKind::F16 { .. } => (),
                FloatKind::F32 { .. } => (),
                FloatKind::F64 { .. } => (),
                FloatKind::F128 { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> () {
        let result = {
            match v {
                Literal::String { .. } => (),
                Literal::Char { .. } => (),
                Literal::Bool { .. } => (),
                Literal::Int {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_int_kind(kind);
                    ()
                }
                Literal::Float {
                    value,
                    negative,
                    kind,
                } => {
                    visitor.visit_float_kind(kind);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> () {
        let result = {
            match v {
                ResugaredTyKind::Unit { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> () {
        let result = {
            match v {
                _ => unreachable!(
                    "references are always considered inhabited, even for an empty enum"
                ),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> () {
        let result = {
            match v {
                GenericValue::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                GenericValue::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                GenericValue::Lifetime { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> () {
        let result = {
            match v {
                PrimitiveTy::Bool { .. } => (),
                PrimitiveTy::Int(anon_field_0) => {
                    visitor.visit_int_kind(anon_field_0);
                    ()
                }
                PrimitiveTy::Float(anon_field_0) => {
                    visitor.visit_float_kind(anon_field_0);
                    ()
                }
                PrimitiveTy::Char { .. } => (),
                PrimitiveTy::Str { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> () {
        let result = {
            match v {
                Region { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(visitor: &mut V, v: &'lt Ty) -> () {
        let result = {
            match v {
                Ty(anon_field_0) => {
                    visitor.visit_ty_kind(anon_field_0.deref());
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> () {
        let result = {
            match v {
                TyKind::Primitive(anon_field_0) => {
                    visitor.visit_primitive_ty(anon_field_0);
                    ()
                }
                TyKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_ty(visitor_item);
                    }
                    ()
                }
                TyKind::App { head, args } => {
                    visitor.visit_global_id(head);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
                TyKind::Arrow { inputs, output } => {
                    for visitor_item in inputs {
                        visitor.visit_ty(visitor_item);
                    }
                    visitor.visit_ty(output);
                    ()
                }
                TyKind::Ref {
                    inner,
                    mutable,
                    region,
                } => {
                    visitor.visit_ty(inner);
                    visitor.visit_region(region);
                    ()
                }
                TyKind::Param(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0);
                    ()
                }
                TyKind::Slice(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                TyKind::Array { ty, length } => {
                    visitor.visit_ty(ty);
                    visitor.visit_expr(length.deref());
                    ()
                }
                TyKind::RawPointer { .. } => (),
                TyKind::AssociatedType { impl_, item } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(item);
                    ()
                }
                TyKind::Opaque(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0);
                    ()
                }
                TyKind::Dyn(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_dyn_trait_goal(visitor_item);
                    }
                    ()
                }
                TyKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_ty_kind(anon_field_0);
                    ()
                }
                TyKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_error_node<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ErrorNode,
    ) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> () {
        let result = {
            match v {
                DynTraitGoal {
                    trait_,
                    non_self_args,
                } => {
                    visitor.visit_global_id(trait_);
                    for visitor_item in non_self_args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> () {
        let result = {
            match v {
                Metadata { span, attributes } => {
                    visitor.visit_span(span);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(visitor: &mut V, v: &'lt Pat) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(visitor: &mut V, v: &'lt Arm) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                visitor.visit_pat(pat);
                visitor.visit_expr(body);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> () {
        let result = {
            match v {
                BorrowKind::Shared { .. } => (),
                BorrowKind::Unique { .. } => (),
                BorrowKind::Mut { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> () {
        let result = {
            match v {
                BindingMode::ByValue { .. } => (),
                BindingMode::ByRef(anon_field_0) => {
                    visitor.visit_borrow_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> () {
        let result = {
            match v {
                PatKind::Wild { .. } => (),
                PatKind::Ascription { pat, ty } => {
                    visitor.visit_pat(pat);
                    visitor.visit_spanned_ty(ty);
                    ()
                }
                PatKind::Or { sub_pats } => {
                    for visitor_item in sub_pats {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Array { args } => {
                    for visitor_item in args {
                        visitor.visit_pat(visitor_item);
                    }
                    ()
                }
                PatKind::Deref { sub_pat } => {
                    visitor.visit_pat(sub_pat);
                    ()
                }
                PatKind::Constant { lit } => {
                    visitor.visit_literal(lit);
                    ()
                }
                PatKind::Binding {
                    mutable,
                    var,
                    mode,
                    sub_pat,
                } => {
                    visitor.visit_local_id(var);
                    visitor.visit_binding_mode(mode);
                    ()
                }
                PatKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                } => {
                    visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_pat(visitor_item_1);
                        };
                    }
                    ()
                }
                PatKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_pat_kind(anon_field_0);
                    ()
                }
                PatKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> () {
        let result = {
            match v {
                GuardKind::IfLet { lhs, rhs } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(visitor: &mut V, v: &'lt Lhs) -> () {
        let result = {
            match v {
                Lhs::LocalVar { var, ty } => {
                    visitor.visit_local_id(var);
                    visitor.visit_ty(ty);
                    ()
                }
                Lhs::ArbitraryExpr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0.deref());
                    ()
                }
                Lhs::FieldAccessor { e, ty, field } => {
                    visitor.visit_lhs(e.deref());
                    visitor.visit_ty(ty);
                    visitor.visit_global_id(field);
                    ()
                }
                Lhs::ArrayAccessor { e, ty, index } => {
                    visitor.visit_lhs(e.deref());
                    visitor.visit_ty(ty);
                    visitor.visit_expr(index);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> () {
        let result = {
            match v {
                ImplExpr { kind, goal } => {
                    visitor.visit_impl_expr_kind(kind.deref());
                    visitor.visit_trait_goal(goal);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> () {
        let result = {
            match v {
                ImplExprKind::Self_ { .. } => (),
                ImplExprKind::Concrete(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0);
                    ()
                }
                ImplExprKind::LocalBound { .. } => (),
                ImplExprKind::Parent { impl_, ident } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_impl_ident(ident);
                    ()
                }
                ImplExprKind::Projection { impl_, item, ident } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(item);
                    visitor.visit_impl_ident(ident);
                    ()
                }
                ImplExprKind::ImplApp { impl_, args } => {
                    visitor.visit_impl_expr(impl_);
                    for visitor_item in args {
                        visitor.visit_impl_expr(visitor_item);
                    }
                    ()
                }
                ImplExprKind::Dyn { .. } => (),
                ImplExprKind::Builtin(anon_field_0) => {
                    visitor.visit_trait_goal(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                visitor.visit_metadata(meta);
                visitor.visit_generics(generics);
                visitor.visit_impl_item_kind(kind);
                visitor.visit_global_id(ident);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> () {
        let result = {
            match v {
                ImplItemKind::Type { ty, parent_bounds } => {
                    visitor.visit_ty(ty);
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0);
                            visitor.visit_impl_ident(visitor_item_1);
                        };
                    }
                    ()
                }
                ImplItemKind::Fn { body, params } => {
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    ()
                }
                ImplItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_impl_item_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                visitor.visit_metadata(meta);
                visitor.visit_trait_item_kind(kind);
                visitor.visit_generics(generics);
                visitor.visit_global_id(ident);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> () {
        let result = {
            match v {
                TraitItemKind::Type(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_impl_ident(visitor_item);
                    }
                    ()
                }
                TraitItemKind::Fn(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
                TraitItemKind::Default { params, body } => {
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    visitor.visit_expr(body);
                    ()
                }
                TraitItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_trait_item_kind(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> () {
        let result = {
            match v {
                QuoteContent::Verbatim { .. } => (),
                QuoteContent::Expr(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                QuoteContent::Pattern(anon_field_0) => {
                    visitor.visit_pat(anon_field_0);
                    ()
                }
                QuoteContent::Ty(anon_field_0) => {
                    visitor.visit_ty(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> () {
        let result = {
            match v {
                Quote(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_quote_content(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOrigin {
                    item_kind,
                    item_ident,
                    position,
                } => {
                    visitor.visit_item_quote_origin_kind(item_kind);
                    visitor.visit_global_id(item_ident);
                    visitor.visit_item_quote_origin_position(position);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginKind::Fn { .. } => (),
                ItemQuoteOriginKind::TyAlias { .. } => (),
                ItemQuoteOriginKind::Type { .. } => (),
                ItemQuoteOriginKind::MacroInvocation { .. } => (),
                ItemQuoteOriginKind::Trait { .. } => (),
                ItemQuoteOriginKind::Impl { .. } => (),
                ItemQuoteOriginKind::Alias { .. } => (),
                ItemQuoteOriginKind::Use { .. } => (),
                ItemQuoteOriginKind::Quote { .. } => (),
                ItemQuoteOriginKind::HaxError { .. } => (),
                ItemQuoteOriginKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> () {
        let result = {
            match v {
                ItemQuoteOriginPosition::Before { .. } => (),
                ItemQuoteOriginPosition::After { .. } => (),
                ItemQuoteOriginPosition::Replace { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> () {
        let result = {
            match v {
                LoopKind::UnconditionalLoop { .. } => (),
                LoopKind::WhileLoop { condition } => {
                    visitor.visit_expr(condition);
                    ()
                }
                LoopKind::ForLoop { pat, iterator } => {
                    visitor.visit_pat(pat);
                    visitor.visit_expr(iterator);
                    ()
                }
                LoopKind::ForIndexLoop {
                    start,
                    end,
                    var,
                    var_ty,
                } => {
                    visitor.visit_expr(start);
                    visitor.visit_expr(end);
                    visitor.visit_local_id(var);
                    visitor.visit_ty(var_ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> () {
        let result = {
            match v {
                ControlFlowKind::BreakOnly { .. } => (),
                ControlFlowKind::BreakOrReturn { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> () {
        let result = {
            match v {
                LoopState { init, body_pat } => {
                    visitor.visit_expr(init);
                    visitor.visit_pat(body_pat);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> () {
        let result = {
            match v {
                ExprKind::If {
                    condition,
                    then,
                    else_,
                } => {
                    visitor.visit_expr(condition);
                    visitor.visit_expr(then);
                    ()
                }
                ExprKind::App {
                    head,
                    args,
                    generic_args,
                    bounds_impls,
                    trait_,
                } => {
                    visitor.visit_expr(head);
                    for visitor_item in args {
                        visitor.visit_expr(visitor_item);
                    }
                    for visitor_item in generic_args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    for visitor_item in bounds_impls {
                        visitor.visit_impl_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Literal(anon_field_0) => {
                    visitor.visit_literal(anon_field_0);
                    ()
                }
                ExprKind::Array(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Construct {
                    constructor,
                    is_record,
                    is_struct,
                    fields,
                    base,
                } => {
                    visitor.visit_global_id(constructor);
                    for visitor_item in fields {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_expr(visitor_item_1);
                        };
                    }
                    ()
                }
                ExprKind::Match { scrutinee, arms } => {
                    visitor.visit_expr(scrutinee);
                    for visitor_item in arms {
                        visitor.visit_arm(visitor_item);
                    }
                    ()
                }
                ExprKind::Tuple(anon_field_0) => {
                    for visitor_item in anon_field_0 {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Borrow { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::AddressOf { mutable, inner } => {
                    visitor.visit_expr(inner);
                    ()
                }
                ExprKind::Deref(anon_field_0) => {
                    visitor.visit_expr(anon_field_0);
                    ()
                }
                ExprKind::Let { lhs, rhs, body } => {
                    visitor.visit_pat(lhs);
                    visitor.visit_expr(rhs);
                    visitor.visit_expr(body);
                    ()
                }
                ExprKind::GlobalId(anon_field_0) => {
                    visitor.visit_global_id(anon_field_0);
                    ()
                }
                ExprKind::LocalId(anon_field_0) => {
                    visitor.visit_local_id(anon_field_0);
                    ()
                }
                ExprKind::Ascription { e, ty } => {
                    visitor.visit_expr(e);
                    visitor.visit_ty(ty);
                    ()
                }
                ExprKind::Assign { lhs, value } => {
                    visitor.visit_lhs(lhs);
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Loop {
                    body,
                    kind,
                    state,
                    control_flow,
                    label,
                } => {
                    visitor.visit_expr(body);
                    visitor.visit_loop_kind(kind);
                    ()
                }
                ExprKind::Break { value, label } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Return { value } => {
                    visitor.visit_expr(value);
                    ()
                }
                ExprKind::Continue { .. } => (),
                ExprKind::Closure {
                    params,
                    body,
                    captures,
                } => {
                    for visitor_item in params {
                        visitor.visit_pat(visitor_item);
                    }
                    visitor.visit_expr(body);
                    for visitor_item in captures {
                        visitor.visit_expr(visitor_item);
                    }
                    ()
                }
                ExprKind::Block { body, safety_mode } => {
                    visitor.visit_expr(body);
                    visitor.visit_safety_kind(safety_mode);
                    ()
                }
                ExprKind::Quote { contents } => {
                    visitor.visit_quote(contents);
                    ()
                }
                ExprKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_expr_kind(anon_field_0);
                    ()
                }
                ExprKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> () {
        let result = {
            match v {
                GenericParamKind::Lifetime { .. } => (),
                GenericParamKind::Type { .. } => (),
                GenericParamKind::Const { ty } => {
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> () {
        let result = {
            match v {
                TraitGoal { trait_, args } => {
                    visitor.visit_global_id(trait_);
                    for visitor_item in args {
                        visitor.visit_generic_value(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> () {
        let result = {
            match v {
                ImplIdent { goal, name } => {
                    visitor.visit_trait_goal(goal);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> () {
        let result = {
            match v {
                ProjectionPredicate {
                    impl_,
                    assoc_item,
                    ty,
                } => {
                    visitor.visit_impl_expr(impl_);
                    visitor.visit_global_id(assoc_item);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> () {
        let result = {
            match v {
                GenericConstraint::Lifetime { .. } => (),
                GenericConstraint::Type(anon_field_0) => {
                    visitor.visit_impl_ident(anon_field_0);
                    ()
                }
                GenericConstraint::Projection(anon_field_0) => {
                    visitor.visit_projection_predicate(anon_field_0);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident);
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        });
        result
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> () {
        let result = {
            match v {
                Generics {
                    params,
                    constraints,
                } => {
                    for visitor_item in params {
                        visitor.visit_generic_param(visitor_item);
                    }
                    for visitor_item in constraints {
                        visitor.visit_generic_constraint(visitor_item);
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> () {
        let result = {
            match v {
                SafetyKind::Safe { .. } => (),
                SafetyKind::Unsafe { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> () {
        let result = {
            match v {
                Attribute { kind, span } => {
                    visitor.visit_attribute_kind(kind);
                    visitor.visit_span(span);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> () {
        let result = {
            match v {
                AttributeKind::Tool { .. } => (),
                AttributeKind::DocComment { kind, body } => {
                    visitor.visit_doc_comment_kind(kind);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> () {
        let result = {
            match v {
                DocCommentKind::Line { .. } => (),
                DocCommentKind::Block { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> () {
        let result = {
            match v {
                SpannedTy { span, ty } => {
                    visitor.visit_span(span);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> () {
        let result = {
            match v {
                Param {
                    pat,
                    ty,
                    ty_span,
                    attributes,
                } => {
                    visitor.visit_pat(pat);
                    visitor.visit_ty(ty);
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> () {
        let result = {
            match v {
                Variant {
                    name,
                    arguments,
                    is_record,
                    attributes,
                } => {
                    visitor.visit_global_id(name);
                    for visitor_item in arguments {
                        {
                            let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                            visitor.visit_global_id(visitor_item_0);
                            visitor.visit_ty(visitor_item_1);
                            ();
                        };
                    }
                    ()
                }
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> () {
        let result = {
            match v {
                ItemKind::Fn {
                    name,
                    generics,
                    body,
                    params,
                    safety,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    visitor.visit_expr(body);
                    for visitor_item in params {
                        visitor.visit_param(visitor_item);
                    }
                    visitor.visit_safety_kind(safety);
                    ()
                }
                ItemKind::TyAlias { name, generics, ty } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    visitor.visit_ty(ty);
                    ()
                }
                ItemKind::Type {
                    name,
                    generics,
                    variants,
                    is_struct,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    for visitor_item in variants {
                        visitor.visit_variant(visitor_item);
                    }
                    ()
                }
                ItemKind::Trait {
                    name,
                    generics,
                    items,
                } => {
                    visitor.visit_global_id(name);
                    visitor.visit_generics(generics);
                    for visitor_item in items {
                        visitor.visit_trait_item(visitor_item);
                    }
                    ()
                }
                ItemKind::Impl {
                    generics,
                    self_ty,
                    of_trait,
                    items,
                    parent_bounds,
                    safety,
                } => {
                    visitor.visit_generics(generics);
                    visitor.visit_ty(self_ty);
                    {
                        let (visitor_item_0, visitor_item_1) = of_trait;
                        visitor.visit_global_id(visitor_item_0);
                        for visitor_item in visitor_item_1 {
                            visitor.visit_generic_value(visitor_item);
                        }
                    };
                    for visitor_item in items {
                        visitor.visit_impl_item(visitor_item);
                    }
                    for visitor_item in parent_bounds {
                        {
                            let (visitor_item_0, visitor_item_1) = visitor_item;
                            visitor.visit_impl_expr(visitor_item_0);
                            visitor.visit_impl_ident(visitor_item_1);
                        };
                    }
                    visitor.visit_safety_kind(safety);
                    ()
                }
                ItemKind::Alias { name, item } => {
                    visitor.visit_global_id(name);
                    visitor.visit_global_id(item);
                    ()
                }
                ItemKind::Use { .. } => (),
                ItemKind::Quote { quote, origin } => {
                    visitor.visit_quote(quote);
                    visitor.visit_item_quote_origin(origin);
                    ()
                }
                ItemKind::Error(anon_field_0) => {
                    visitor.visit_error_node(anon_field_0);
                    ()
                }
                ItemKind::Resugared(anon_field_0) => {
                    visitor.visit_resugared_item_kind(anon_field_0);
                    ()
                }
                ItemKind::NotImplementedYet { .. } => (),
            }
        };
        result
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Vanilla<'lt> + ?Sized + HasSpan>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> () {
        let result = with_span(visitor, v.span(), |visitor| match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident);
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        });
        result
    }
}
