pub mod map_reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapReduceCf {
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
    pub fn visit_global_id<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GlobalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut LocalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut IntSize,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            IntSize::S8 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::SSize { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Signedness,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Signedness::Signed { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut IntKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            IntKind { size, signedness } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_int_size(size)?;
                visitor_reduce_value.append(visitor.visit_signedness(signedness)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut FloatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Literal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Span,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Ty,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
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
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Metadata { span, attributes } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut())?;
                visitor_reduce_value.append(visitor.visit_trait_goal(goal)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                visitor_reduce_value.append(visitor.visit_global_id(item_ident)?);
                visitor_reduce_value.append(visitor.visit_item_quote_origin_position(position)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::TyAlias { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::MacroInvocation { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Trait { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::Alias { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ControlFlowKind::BreakOnly { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ControlFlowKind::BreakOrReturn { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr(init)?;
                visitor_reduce_value.append(visitor.visit_pat(body_pat)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GenericParamKind::Lifetime { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
                    visitor_reduce_value.append(visitor.visit_generic_constraint(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_span(span)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span)?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Param,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemKind::Resugared(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::NotImplementedYet { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduceCf + ?Sized>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident)?;
                visitor_reduce_value.append(visitor.visit_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
}
pub mod map_cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait MapCf {
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
    pub fn visit_global_id<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GlobalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut LocalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut IntSize,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            IntSize::S8 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S16 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S32 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S64 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S128 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::SSize { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Signedness,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Signedness::Signed { .. } => std::ops::ControlFlow::Continue(()),
            Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut IntKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            IntKind { size, signedness } => {
                visitor.visit_int_size(size)?;
                visitor.visit_signedness(signedness)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut FloatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Literal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Span,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_region<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Ty,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref_mut())?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                visitor.visit_primitive_ty(anon_field_0)?;
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
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Metadata { span, attributes } => {
                visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref_mut())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref_mut())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(()),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs)?;
                visitor.visit_expr(rhs)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref_mut())?;
                visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Quote(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_quote_content(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ItemQuoteOriginKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ItemQuoteOriginPosition::Before { .. } => std::ops::ControlFlow::Continue(()),
            ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(()),
            ItemQuoteOriginPosition::Replace { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init)?;
                visitor.visit_pat(body_pat)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ExprKind::Borrow { mutable, inner } => {
                visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(())
            }
            ExprKind::AddressOf { mutable, inner } => {
                visitor.visit_expr(inner)?;
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(()),
            GenericParamKind::Const { ty } => {
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TraitGoal { trait_, args } => {
                visitor.visit_global_id(trait_)?;
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident)?;
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind)?;
                visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(()),
            AttributeKind::DocComment { kind, body } => {
                visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_span(span)?;
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Param,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Resugared(anon_field_0) => {
                visitor.visit_resugared_item_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: MapCf + ?Sized>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident)?;
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
}
pub mod reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait ReduceCf<'lt> {
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
    pub fn visit_global_id<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            IntSize::S8 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::S128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            IntSize::SSize { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Signedness::Signed { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            IntKind { size, signedness } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_int_size(size)?;
                visitor_reduce_value.append(visitor.visit_signedness(signedness)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        let _ = v;
        std::ops::ControlFlow::Continue(V::Out::identity())
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
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
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Metadata { span, attributes } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref())?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                visitor_reduce_value.append(visitor.visit_expr(rhs)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref())?;
                visitor_reduce_value.append(visitor.visit_trait_goal(goal)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                visitor_reduce_value.append(visitor.visit_global_id(item_ident)?);
                visitor_reduce_value.append(visitor.visit_item_quote_origin_position(position)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::TyAlias { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::MacroInvocation { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Trait { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemQuoteOriginKind::Alias { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ControlFlowKind::BreakOnly { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            ControlFlowKind::BreakOrReturn { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr(init)?;
                visitor_reduce_value.append(visitor.visit_pat(body_pat)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GenericParamKind::Lifetime { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident)?;
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
                    visitor_reduce_value.append(visitor.visit_generic_constraint(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                visitor_reduce_value.append(visitor.visit_span(span)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span)?;
                visitor_reduce_value.append(visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
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
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(V::Out::identity()),
            ItemKind::Resugared(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::NotImplementedYet { .. } => {
                std::ops::ControlFlow::Continue(V::Out::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: ReduceCf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, V::Out> {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident)?;
                visitor_reduce_value.append(visitor.visit_item_kind(kind)?);
                visitor_reduce_value.append(visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
}
pub mod cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait Cf<'lt> {
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
    pub fn visit_global_id<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            IntSize::S8 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S16 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S32 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S64 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::S128 { .. } => std::ops::ControlFlow::Continue(()),
            IntSize::SSize { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Signedness::Signed { .. } => std::ops::ControlFlow::Continue(()),
            Signedness::Unsigned { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            IntKind { size, signedness } => {
                visitor.visit_int_size(size)?;
                visitor.visit_signedness(signedness)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            FloatKind::F16 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F32 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F64 { .. } => std::ops::ControlFlow::Continue(()),
            FloatKind::F128 { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Literal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ResugaredTyKind::Unit { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Span,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        let _ = v;
        std::ops::ControlFlow::Continue(())
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref())?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                visitor.visit_primitive_ty(anon_field_0)?;
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
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Metadata { span, attributes } => {
                visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref())?;
                visitor.visit_ty(ty)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(()),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs)?;
                visitor.visit_expr(rhs)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref())?;
                visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Quote(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_quote_content(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ItemQuoteOriginKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ItemQuoteOriginPosition::Before { .. } => std::ops::ControlFlow::Continue(()),
            ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(()),
            ItemQuoteOriginPosition::Replace { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init)?;
                visitor.visit_pat(body_pat)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ExprKind::Borrow { mutable, inner } => {
                visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(())
            }
            ExprKind::AddressOf { mutable, inner } => {
                visitor.visit_expr(inner)?;
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(()),
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(()),
            GenericParamKind::Const { ty } => {
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TraitGoal { trait_, args } => {
                visitor.visit_global_id(trait_)?;
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident)?;
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind)?;
                visitor.visit_span(span)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(()),
            AttributeKind::DocComment { kind, body } => {
                visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_span(span)?;
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Resugared(anon_field_0) => {
                visitor.visit_resugared_item_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Cf<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident)?;
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
}
pub mod map_reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait MapReduce {
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
    pub fn visit_global_id<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut GlobalId) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut LocalId) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut IntSize) -> V::Out {
        match v {
            IntSize::S8 { .. } => V::Out::identity(),
            IntSize::S16 { .. } => V::Out::identity(),
            IntSize::S32 { .. } => V::Out::identity(),
            IntSize::S64 { .. } => V::Out::identity(),
            IntSize::S128 { .. } => V::Out::identity(),
            IntSize::SSize { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Signedness) -> V::Out {
        match v {
            Signedness::Signed { .. } => V::Out::identity(),
            Signedness::Unsigned { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut IntKind) -> V::Out {
        match v {
            IntKind { size, signedness } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_int_size(size);
                visitor_reduce_value.append(visitor.visit_signedness(signedness));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut FloatKind) -> V::Out {
        match v {
            FloatKind::F16 { .. } => V::Out::identity(),
            FloatKind::F32 { .. } => V::Out::identity(),
            FloatKind::F64 { .. } => V::Out::identity(),
            FloatKind::F128 { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Literal) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> V::Out {
        match v {
            ResugaredTyKind::Unit { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Span) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_region<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Region) -> V::Out {
        match v {
            Region { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Ty) -> V::Out {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut());
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut TyKind) -> V::Out {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
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
            TyKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Metadata) -> V::Out {
        match v {
            Metadata { span, attributes } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Expr) -> V::Out {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Pat) -> V::Out {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Arm) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Guard) -> V::Out {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut BorrowKind) -> V::Out {
        match v {
            BorrowKind::Shared { .. } => V::Out::identity(),
            BorrowKind::Unique { .. } => V::Out::identity(),
            BorrowKind::Mut { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> V::Out {
        match v {
            BindingMode::ByValue { .. } => V::Out::identity(),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut PatKind) -> V::Out {
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
            PatKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut GuardKind) -> V::Out {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(lhs);
                visitor_reduce_value.append(visitor.visit_expr(rhs));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Lhs) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut ImplExpr) -> V::Out {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut());
                visitor_reduce_value.append(visitor.visit_trait_goal(goal));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut ImplItem) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut TraitItem) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_quote<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Quote) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> V::Out {
        match v {
            ItemQuoteOriginPosition::Before { .. } => V::Out::identity(),
            ItemQuoteOriginPosition::After { .. } => V::Out::identity(),
            ItemQuoteOriginPosition::Replace { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut LoopKind) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> V::Out {
        match v {
            ControlFlowKind::BreakOnly { .. } => V::Out::identity(),
            ControlFlowKind::BreakOrReturn { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut LoopState) -> V::Out {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr(init);
                visitor_reduce_value.append(visitor.visit_pat(body_pat));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut ExprKind) -> V::Out {
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> V::Out {
        match v {
            GenericParamKind::Lifetime { .. } => V::Out::identity(),
            GenericParamKind::Type { .. } => V::Out::identity(),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut TraitGoal) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut ImplIdent) -> V::Out {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(goal);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> V::Out {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Generics) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut SafetyKind) -> V::Out {
        match v {
            SafetyKind::Safe { .. } => V::Out::identity(),
            SafetyKind::Unsafe { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Attribute) -> V::Out {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_attribute_kind(kind);
                visitor_reduce_value.append(visitor.visit_span(span));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> V::Out {
        match v {
            AttributeKind::Tool { .. } => V::Out::identity(),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: MapReduce + ?Sized>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> V::Out {
        match v {
            DocCommentKind::Line { .. } => V::Out::identity(),
            DocCommentKind::Block { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut SpannedTy) -> V::Out {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span);
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Param) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_variant<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Variant) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut ItemKind) -> V::Out {
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
            ItemKind::Error { .. } => V::Out::identity(),
            ItemKind::Resugared(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0);
                visitor_reduce_value
            }
            ItemKind::NotImplementedYet { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: MapReduce + ?Sized>(visitor: &mut V, v: &mut Item) -> V::Out {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident);
                visitor_reduce_value.append(visitor.visit_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
}
pub mod map {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait Map {
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
    pub fn visit_global_id<V: Map + ?Sized>(visitor: &mut V, v: &mut GlobalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_local_id<V: Map + ?Sized>(visitor: &mut V, v: &mut LocalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_int_size<V: Map + ?Sized>(visitor: &mut V, v: &mut IntSize) -> () {
        match v {
            IntSize::S8 { .. } => (),
            IntSize::S16 { .. } => (),
            IntSize::S32 { .. } => (),
            IntSize::S64 { .. } => (),
            IntSize::S128 { .. } => (),
            IntSize::SSize { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<V: Map + ?Sized>(visitor: &mut V, v: &mut Signedness) -> () {
        match v {
            Signedness::Signed { .. } => (),
            Signedness::Unsigned { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut IntKind) -> () {
        match v {
            IntKind { size, signedness } => {
                visitor.visit_int_size(size);
                visitor.visit_signedness(signedness);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut FloatKind) -> () {
        match v {
            FloatKind::F16 { .. } => (),
            FloatKind::F32 { .. } => (),
            FloatKind::F64 { .. } => (),
            FloatKind::F128 { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<V: Map + ?Sized>(visitor: &mut V, v: &mut Literal) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredExprKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredPatKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTyKind,
    ) -> () {
        match v {
            ResugaredTyKind::Unit { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredImplItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ResugaredTraitItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<V: Map + ?Sized>(visitor: &mut V, v: &mut Span) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: Map + ?Sized>(visitor: &mut V, v: &mut GenericValue) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: Map + ?Sized>(visitor: &mut V, v: &mut PrimitiveTy) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_region<V: Map + ?Sized>(visitor: &mut V, v: &mut Region) -> () {
        match v {
            Region { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: Map + ?Sized>(visitor: &mut V, v: &mut Ty) -> () {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref_mut());
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut TyKind) -> () {
        match v {
            TyKind::Primitive(anon_field_0) => {
                visitor.visit_primitive_ty(anon_field_0);
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
            TyKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: Map + ?Sized>(visitor: &mut V, v: &mut DynTraitGoal) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<V: Map + ?Sized>(visitor: &mut V, v: &mut Metadata) -> () {
        match v {
            Metadata { span, attributes } => {
                visitor.visit_span(span);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: Map + ?Sized>(visitor: &mut V, v: &mut Expr) -> () {
        match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref_mut());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: Map + ?Sized>(visitor: &mut V, v: &mut Pat) -> () {
        match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref_mut());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: Map + ?Sized>(visitor: &mut V, v: &mut Arm) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: Map + ?Sized>(visitor: &mut V, v: &mut Guard) -> () {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut BorrowKind) -> () {
        match v {
            BorrowKind::Shared { .. } => (),
            BorrowKind::Unique { .. } => (),
            BorrowKind::Mut { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: Map + ?Sized>(visitor: &mut V, v: &mut BindingMode) -> () {
        match v {
            BindingMode::ByValue { .. } => (),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut PatKind) -> () {
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
            PatKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut GuardKind) -> () {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs);
                visitor.visit_expr(rhs);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: Map + ?Sized>(visitor: &mut V, v: &mut Lhs) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: Map + ?Sized>(visitor: &mut V, v: &mut ImplExpr) -> () {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref_mut());
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut ImplExprKind) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: Map + ?Sized>(visitor: &mut V, v: &mut ImplItem) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut ImplItemKind) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: Map + ?Sized>(visitor: &mut V, v: &mut TraitItem) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut TraitItemKind) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: Map + ?Sized>(visitor: &mut V, v: &mut QuoteContent) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_quote<V: Map + ?Sized>(visitor: &mut V, v: &mut Quote) -> () {
        match v {
            Quote(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_quote_content(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> () {
        match v {
            ItemQuoteOriginPosition::Before { .. } => (),
            ItemQuoteOriginPosition::After { .. } => (),
            ItemQuoteOriginPosition::Replace { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut LoopKind) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> () {
        match v {
            ControlFlowKind::BreakOnly { .. } => (),
            ControlFlowKind::BreakOrReturn { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: Map + ?Sized>(visitor: &mut V, v: &mut LoopState) -> () {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init);
                visitor.visit_pat(body_pat);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut ExprKind) -> () {
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
            ExprKind::Borrow { mutable, inner } => {
                visitor.visit_expr(inner);
                ()
            }
            ExprKind::AddressOf { mutable, inner } => {
                visitor.visit_expr(inner);
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> () {
        match v {
            GenericParamKind::Lifetime { .. } => (),
            GenericParamKind::Type { .. } => (),
            GenericParamKind::Const { ty } => {
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: Map + ?Sized>(visitor: &mut V, v: &mut TraitGoal) -> () {
        match v {
            TraitGoal { trait_, args } => {
                visitor.visit_global_id(trait_);
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: Map + ?Sized>(visitor: &mut V, v: &mut ImplIdent) -> () {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: Map + ?Sized>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: Map + ?Sized>(visitor: &mut V, v: &mut GenericParam) -> () {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident);
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: Map + ?Sized>(visitor: &mut V, v: &mut Generics) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut SafetyKind) -> () {
        match v {
            SafetyKind::Safe { .. } => (),
            SafetyKind::Unsafe { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: Map + ?Sized>(visitor: &mut V, v: &mut Attribute) -> () {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind);
                visitor.visit_span(span);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut AttributeKind) -> () {
        match v {
            AttributeKind::Tool { .. } => (),
            AttributeKind::DocComment { kind, body } => {
                visitor.visit_doc_comment_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut DocCommentKind) -> () {
        match v {
            DocCommentKind::Line { .. } => (),
            DocCommentKind::Block { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: Map + ?Sized>(visitor: &mut V, v: &mut SpannedTy) -> () {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_span(span);
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: Map + ?Sized>(visitor: &mut V, v: &mut Param) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_variant<V: Map + ?Sized>(visitor: &mut V, v: &mut Variant) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: Map + ?Sized>(visitor: &mut V, v: &mut ItemKind) -> () {
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
            ItemKind::Error { .. } => (),
            ItemKind::Resugared(anon_field_0) => {
                visitor.visit_resugared_item_kind(anon_field_0);
                ()
            }
            ItemKind::NotImplementedYet { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: Map + ?Sized>(visitor: &mut V, v: &mut Item) -> () {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident);
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
}
pub mod reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait Reduce<'lt> {
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
    pub fn visit_global_id<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GlobalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LocalId,
    ) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntSize,
    ) -> V::Out {
        match v {
            IntSize::S8 { .. } => V::Out::identity(),
            IntSize::S16 { .. } => V::Out::identity(),
            IntSize::S32 { .. } => V::Out::identity(),
            IntSize::S64 { .. } => V::Out::identity(),
            IntSize::S128 { .. } => V::Out::identity(),
            IntSize::SSize { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> V::Out {
        match v {
            Signedness::Signed { .. } => V::Out::identity(),
            Signedness::Unsigned { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt IntKind,
    ) -> V::Out {
        match v {
            IntKind { size, signedness } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_int_size(size);
                visitor_reduce_value.append(visitor.visit_signedness(signedness));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> V::Out {
        match v {
            FloatKind::F16 { .. } => V::Out::identity(),
            FloatKind::F32 { .. } => V::Out::identity(),
            FloatKind::F64 { .. } => V::Out::identity(),
            FloatKind::F128 { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Literal) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> V::Out {
        match v {
            ResugaredTyKind::Unit { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> V::Out {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Span) -> V::Out {
        let _ = v;
        V::Out::identity()
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Region) -> V::Out {
        match v {
            Region { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Ty) -> V::Out {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref());
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt TyKind) -> V::Out {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
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
            TyKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> V::Out {
        match v {
            Metadata { span, attributes } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Expr) -> V::Out {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Pat) -> V::Out {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref());
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Arm) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Guard) -> V::Out {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> V::Out {
        match v {
            BorrowKind::Shared { .. } => V::Out::identity(),
            BorrowKind::Unique { .. } => V::Out::identity(),
            BorrowKind::Mut { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> V::Out {
        match v {
            BindingMode::ByValue { .. } => V::Out::identity(),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> V::Out {
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
            PatKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> V::Out {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_pat(lhs);
                visitor_reduce_value.append(visitor.visit_expr(rhs));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Lhs) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> V::Out {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref());
                visitor_reduce_value.append(visitor.visit_trait_goal(goal));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> V::Out {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Quote) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> V::Out {
        match v {
            ItemQuoteOriginPosition::Before { .. } => V::Out::identity(),
            ItemQuoteOriginPosition::After { .. } => V::Out::identity(),
            ItemQuoteOriginPosition::Replace { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> V::Out {
        match v {
            ControlFlowKind::BreakOnly { .. } => V::Out::identity(),
            ControlFlowKind::BreakOrReturn { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> V::Out {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_expr(init);
                visitor_reduce_value.append(visitor.visit_pat(body_pat));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> V::Out {
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> V::Out {
        match v {
            GenericParamKind::Lifetime { .. } => V::Out::identity(),
            GenericParamKind::Type { .. } => V::Out::identity(),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> V::Out {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_trait_goal(goal);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> V::Out {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_local_id(ident);
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value.append(visitor.visit_generic_param_kind(kind));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> V::Out {
        match v {
            SafetyKind::Safe { .. } => V::Out::identity(),
            SafetyKind::Unsafe { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> V::Out {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_attribute_kind(kind);
                visitor_reduce_value.append(visitor.visit_span(span));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> V::Out {
        match v {
            AttributeKind::Tool { .. } => V::Out::identity(),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> V::Out {
        match v {
            DocCommentKind::Line { .. } => V::Out::identity(),
            DocCommentKind::Block { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> V::Out {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_span(span);
                visitor_reduce_value.append(visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Param) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Variant) -> V::Out {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Reduce<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> V::Out {
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
            ItemKind::Error { .. } => V::Out::identity(),
            ItemKind::Resugared(anon_field_0) => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_resugared_item_kind(anon_field_0);
                visitor_reduce_value
            }
            ItemKind::NotImplementedYet { .. } => V::Out::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Reduce<'lt> + ?Sized>(visitor: &mut V, v: &'lt Item) -> V::Out {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: V::Out;
                visitor_reduce_value = visitor.visit_global_id(ident);
                visitor_reduce_value.append(visitor.visit_item_kind(kind));
                visitor_reduce_value.append(visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
}
pub mod vanilla {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait Vanilla<'lt> {
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
    pub fn visit_global_id<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt GlobalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_local_id<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt LocalId) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_int_size<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt IntSize) -> () {
        match v {
            IntSize::S8 { .. } => (),
            IntSize::S16 { .. } => (),
            IntSize::S32 { .. } => (),
            IntSize::S64 { .. } => (),
            IntSize::S128 { .. } => (),
            IntSize::SSize { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_signedness<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Signedness,
    ) -> () {
        match v {
            Signedness::Signed { .. } => (),
            Signedness::Unsigned { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_int_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt IntKind) -> () {
        match v {
            IntKind { size, signedness } => {
                visitor.visit_int_size(size);
                visitor.visit_signedness(signedness);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_float_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt FloatKind,
    ) -> () {
        match v {
            FloatKind::F16 { .. } => (),
            FloatKind::F32 { .. } => (),
            FloatKind::F64 { .. } => (),
            FloatKind::F128 { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_literal<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Literal) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_resugared_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_expr_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredExprKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_pat_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredPatKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_ty_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTyKind,
    ) -> () {
        match v {
            ResugaredTyKind::Unit { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_impl_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredImplItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_resugared_trait_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ResugaredTraitItemKind,
    ) -> () {
        match v {
            _ => unreachable!("references are always considered inhabited, even for an empty enum"),
        }
    }
    #[allow(unused)]
    pub fn visit_span<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Span) -> () {
        let _ = v;
        ()
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Region) -> () {
        match v {
            Region { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Ty) -> () {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref());
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt TyKind) -> () {
        match v {
            TyKind::Primitive(anon_field_0) => {
                visitor.visit_primitive_ty(anon_field_0);
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
            TyKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Metadata) -> () {
        match v {
            Metadata { span, attributes } => {
                visitor.visit_span(span);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Expr) -> () {
        match v {
            Expr { kind, ty, meta } => {
                visitor.visit_expr_kind(kind.deref());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Pat) -> () {
        match v {
            Pat { kind, ty, meta } => {
                visitor.visit_pat_kind(kind.deref());
                visitor.visit_ty(ty);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Arm) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Guard) -> () {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> () {
        match v {
            BorrowKind::Shared { .. } => (),
            BorrowKind::Unique { .. } => (),
            BorrowKind::Mut { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> () {
        match v {
            BindingMode::ByValue { .. } => (),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt PatKind) -> () {
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
            PatKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> () {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs);
                visitor.visit_expr(rhs);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Lhs) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt ImplExpr) -> () {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref());
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt ImplItem) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> () {
        match v {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Quote) -> () {
        match v {
            Quote(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_quote_content(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> () {
        match v {
            ItemQuoteOriginPosition::Before { .. } => (),
            ItemQuoteOriginPosition::After { .. } => (),
            ItemQuoteOriginPosition::Replace { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt LoopKind) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> () {
        match v {
            ControlFlowKind::BreakOnly { .. } => (),
            ControlFlowKind::BreakOrReturn { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> () {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init);
                visitor.visit_pat(body_pat);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt ExprKind) -> () {
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
            ExprKind::Borrow { mutable, inner } => {
                visitor.visit_expr(inner);
                ()
            }
            ExprKind::AddressOf { mutable, inner } => {
                visitor.visit_expr(inner);
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
            ExprKind::Break {
                value,
                label,
                state,
            } => {
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
            ExprKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> () {
        match v {
            GenericParamKind::Lifetime { .. } => (),
            GenericParamKind::Type { .. } => (),
            GenericParamKind::Const { ty } => {
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> () {
        match v {
            TraitGoal { trait_, args } => {
                visitor.visit_global_id(trait_);
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> () {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> () {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_local_id(ident);
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Generics) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> () {
        match v {
            SafetyKind::Safe { .. } => (),
            SafetyKind::Unsafe { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> () {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind);
                visitor.visit_span(span);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> () {
        match v {
            AttributeKind::Tool { .. } => (),
            AttributeKind::DocComment { kind, body } => {
                visitor.visit_doc_comment_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> () {
        match v {
            DocCommentKind::Line { .. } => (),
            DocCommentKind::Block { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Vanilla<'lt> + ?Sized>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> () {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_span(span);
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Param) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Variant) -> () {
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
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt ItemKind) -> () {
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
            ItemKind::Error { .. } => (),
            ItemKind::Resugared(anon_field_0) => {
                visitor.visit_resugared_item_kind(anon_field_0);
                ()
            }
            ItemKind::NotImplementedYet { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Vanilla<'lt> + ?Sized>(visitor: &mut V, v: &'lt Item) -> () {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_global_id(ident);
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
}
