mod visitor_map_reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait VisitorMapReduceCf: Sized + Monoid {
        type Error;
        fn visit_generic_value(
            &mut self,
            v: &mut GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &mut PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(
            &mut self,
            v: &mut Region,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_region(self, v)
        }
        fn visit_ty(
            &mut self,
            v: &mut Ty,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(
            &mut self,
            v: &mut TyKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_ty_kind(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &mut DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(
            &mut self,
            v: &mut Metadata,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_metadata(self, v)
        }
        fn visit_expr(
            &mut self,
            v: &mut Expr,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_expr(self, v)
        }
        fn visit_pat(
            &mut self,
            v: &mut Pat,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_pat(self, v)
        }
        fn visit_arm(
            &mut self,
            v: &mut Arm,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_arm(self, v)
        }
        fn visit_guard(
            &mut self,
            v: &mut Guard,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &mut BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &mut BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(
            &mut self,
            v: &mut PatKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &mut GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(
            &mut self,
            v: &mut Lhs,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(
            &mut self,
            v: &mut ImplExpr,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &mut ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(
            &mut self,
            v: &mut ImplItem,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &mut ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &mut TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &mut TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &mut QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_quote_content(self, v)
        }
        fn visit_quote(
            &mut self,
            v: &mut Quote,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &mut ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(
            &mut self,
            v: &mut LoopKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &mut ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &mut LoopState,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(
            &mut self,
            v: &mut ExprKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &mut GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &mut TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &mut ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &mut GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &mut GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_param(self, v)
        }
        fn visit_generics(
            &mut self,
            v: &mut Generics,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &mut SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(
            &mut self,
            v: &mut Attribute,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &mut AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &mut DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &mut SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(
            &mut self,
            v: &mut Param,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_param(self, v)
        }
        fn visit_variant(
            &mut self,
            v: &mut Variant,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_variant(self, v)
        }
        fn visit_item_kind(
            &mut self,
            v: &mut ItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_kind(self, v)
        }
        fn visit_item(
            &mut self,
            v: &mut Item,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericValue::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericValue::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Int { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Float { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_region<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Ty,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::App { head, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Arrow { inputs, output } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in inputs {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item)?);
                }
                V::append(&mut visitor_reduce_value, visitor.visit_ty(output)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(inner)?;
                V::append(&mut visitor_reduce_value, visitor.visit_region(region)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Param { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::Slice(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Array { ty, length } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_expr(length.deref_mut())?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::AssociatedType { impl_, item } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Opaque { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::Dyn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_dyn_trait_goal(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in non_self_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Metadata { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            PatKind::Wild { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PatKind::Ascription { pat, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_spanned_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Or { sub_pats } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in sub_pats {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Array { args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Deref { sub_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(sub_pat)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Constant { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_binding_mode(mode)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_pat(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Lhs::LocalVar { var, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::ArbitraryExpr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::FieldAccessor { e, ty, field } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref_mut())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::ArrayAccessor { e, ty, index } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref_mut())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(index)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut())?;
                V::append(&mut visitor_reduce_value, visitor.visit_trait_goal(goal)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Parent { impl_, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::Projection { impl_, item, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::ImplApp { impl_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Builtin(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics)?);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_impl_item_kind(kind)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplItemKind::Type { ty, parent_bounds } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0)?,
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplItemKind::Fn { body, params } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_trait_item_kind(kind)?,
                );
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitItemKind::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_ident(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TraitItemKind::Fn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TraitItemKind::Default { params, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(V::identity()),
            QuoteContent::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            QuoteContent::Pattern(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            QuoteContent::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Quote(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_quote_content(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin_position(position)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::TyAlias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::MacroInvocation { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
            ItemQuoteOriginKind::Trait { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Alias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Quote { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::HaxError { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::NotImplementedYet { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOriginPosition::Before { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
            ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginPosition::Replace { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            LoopKind::UnconditionalLoop { .. } => std::ops::ControlFlow::Continue(V::identity()),
            LoopKind::WhileLoop { condition } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            LoopKind::ForLoop { pat, iterator } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(iterator)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            LoopKind::ForIndexLoop {
                start,
                end,
                var,
                var_ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(start)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(end)?);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(var_ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(init)?;
                V::append(&mut visitor_reduce_value, visitor.visit_pat(body_pat)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(then)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(head)?;
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                for visitor_item in generic_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                for visitor_item in bounds_impls {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Literal { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Array(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_expr(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Match { scrutinee, arms } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(scrutinee)?;
                for visitor_item in arms {
                    V::append(&mut visitor_reduce_value, visitor.visit_arm(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Borrow { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::AddressOf { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Deref(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Let { lhs, rhs, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs)?);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::GlobalId { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::LocalId { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Ascription { e, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(e)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Assign { lhs, value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(value)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                V::append(&mut visitor_reduce_value, visitor.visit_loop_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Break { value, label } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Return { value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                for visitor_item in captures {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Block { body, safety_mode } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety_mode)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Quote { contents } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(contents)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitGoal { trait_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ProjectionPredicate {
                impl_,
                assoc_item,
                ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericConstraint::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericConstraint::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_ident(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericConstraint::Projection(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_generic_param_kind(kind)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Generics {
                params,
                constraints,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_param(visitor_item)?,
                    );
                }
                for visitor_item in constraints {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_constraint(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::identity()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::identity()),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::identity()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Param,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Param {
                pat,
                ty,
                ty_span,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_variant<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item_1)?);
                        ();
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::TyAlias { name, generics, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                for visitor_item in variants {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_variant(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Trait {
                name,
                generics,
                items,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_trait_item(visitor_item)?,
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(self_ty)?);
                {
                    let (visitor_item_0, visitor_item_1) = of_trait;
                    ();
                    for visitor_item in visitor_item_1 {
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_generic_value(visitor_item)?,
                        );
                    }
                };
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_item(visitor_item)?,
                    );
                }
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0)?,
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1)?,
                        );
                    };
                }
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Alias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::Use { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::Quote { quote, origin } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(quote)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin(origin)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: VisitorMapReduceCf + Monoid>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_kind(kind)?;
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
}
mod visitor_map_cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait VisitorMapCf: Sized {
        type Error;
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
    pub fn visit_generic_value<V: VisitorMapCf>(
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
    pub fn visit_primitive_ty<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Int { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Float { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_region<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: VisitorMapCf>(
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
    pub fn visit_ty_kind<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            TyKind::Param { .. } => std::ops::ControlFlow::Continue(()),
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
                std::ops::ControlFlow::Continue(())
            }
            TyKind::Opaque { .. } => std::ops::ControlFlow::Continue(()),
            TyKind::Dyn(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_dyn_trait_goal(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                for visitor_item in non_self_args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Metadata { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: VisitorMapCf>(
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
    pub fn visit_pat<V: VisitorMapCf>(
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
    pub fn visit_arm<V: VisitorMapCf>(
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
    pub fn visit_guard<V: VisitorMapCf>(
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
    pub fn visit_borrow_kind<V: VisitorMapCf>(
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
    pub fn visit_binding_mode<V: VisitorMapCf>(
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
    pub fn visit_pat_kind<V: VisitorMapCf>(
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
            PatKind::Constant { .. } => std::ops::ControlFlow::Continue(()),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                visitor.visit_binding_mode(mode)?;
                std::ops::ControlFlow::Continue(())
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        visitor.visit_pat(visitor_item_1)?;
                    };
                }
                std::ops::ControlFlow::Continue(())
            }
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: VisitorMapCf>(
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
    pub fn visit_lhs<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Lhs::LocalVar { var, ty } => {
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
    pub fn visit_impl_expr<V: VisitorMapCf>(
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
    pub fn visit_impl_expr_kind<V: VisitorMapCf>(
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
    pub fn visit_impl_item<V: VisitorMapCf>(
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
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: VisitorMapCf>(
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: VisitorMapCf>(
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
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: VisitorMapCf>(
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
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: VisitorMapCf>(
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
    pub fn visit_quote<V: VisitorMapCf>(
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
    pub fn visit_item_quote_origin<V: VisitorMapCf>(
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
                visitor.visit_item_quote_origin_position(position)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: VisitorMapCf>(
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
    pub fn visit_item_quote_origin_position<V: VisitorMapCf>(
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
    pub fn visit_loop_kind<V: VisitorMapCf>(
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
                visitor.visit_ty(var_ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: VisitorMapCf>(
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
    pub fn visit_expr_kind<V: VisitorMapCf>(
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
            ExprKind::Literal { .. } => std::ops::ControlFlow::Continue(()),
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
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
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
            ExprKind::GlobalId { .. } => std::ops::ControlFlow::Continue(()),
            ExprKind::LocalId { .. } => std::ops::ControlFlow::Continue(()),
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: VisitorMapCf>(
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
    pub fn visit_trait_goal<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TraitGoal { trait_, args } => {
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: VisitorMapCf>(
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
    pub fn visit_projection_predicate<V: VisitorMapCf>(
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
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: VisitorMapCf>(
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
    pub fn visit_generic_param<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: VisitorMapCf>(
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
    pub fn visit_safety_kind<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: VisitorMapCf>(
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
    pub fn visit_doc_comment_kind<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: VisitorMapCf>(
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
    pub fn visit_variant<V: VisitorMapCf>(
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
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        visitor.visit_ty(visitor_item_1)?;
                        ();
                    };
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: VisitorMapCf>(
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
                visitor.visit_generics(generics)?;
                visitor.visit_expr(body)?;
                for visitor_item in params {
                    visitor.visit_param(visitor_item)?;
                }
                visitor.visit_safety_kind(safety)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::TyAlias { name, generics, ty } => {
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
                    ();
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
            ItemKind::Alias { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Use { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Quote { quote, origin } => {
                visitor.visit_quote(quote)?;
                visitor.visit_item_quote_origin(origin)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: VisitorMapCf>(
        visitor: &mut V,
        v: &mut Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
}
mod visitor_reduce_cf {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait VisitorReduceCf<'lt>: Sized + Monoid {
        type Error;
        fn visit_generic_value(
            &mut self,
            v: &'lt GenericValue,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(
            &mut self,
            v: &'lt PrimitiveTy,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_primitive_ty(self, v)
        }
        fn visit_region(
            &mut self,
            v: &'lt Region,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_region(self, v)
        }
        fn visit_ty(
            &mut self,
            v: &'lt Ty,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_ty(self, v)
        }
        fn visit_ty_kind(
            &mut self,
            v: &'lt TyKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_ty_kind(self, v)
        }
        fn visit_dyn_trait_goal(
            &mut self,
            v: &'lt DynTraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(
            &mut self,
            v: &'lt Metadata,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_metadata(self, v)
        }
        fn visit_expr(
            &mut self,
            v: &'lt Expr,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_expr(self, v)
        }
        fn visit_pat(
            &mut self,
            v: &'lt Pat,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_pat(self, v)
        }
        fn visit_arm(
            &mut self,
            v: &'lt Arm,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_arm(self, v)
        }
        fn visit_guard(
            &mut self,
            v: &'lt Guard,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(
            &mut self,
            v: &'lt BorrowKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(
            &mut self,
            v: &'lt BindingMode,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(
            &mut self,
            v: &'lt PatKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(
            &mut self,
            v: &'lt GuardKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(
            &mut self,
            v: &'lt Lhs,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(
            &mut self,
            v: &'lt ImplExpr,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(
            &mut self,
            v: &'lt ImplExprKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(
            &mut self,
            v: &'lt ImplItem,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(
            &mut self,
            v: &'lt ImplItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(
            &mut self,
            v: &'lt TraitItem,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(
            &mut self,
            v: &'lt TraitItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(
            &mut self,
            v: &'lt QuoteContent,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_quote_content(self, v)
        }
        fn visit_quote(
            &mut self,
            v: &'lt Quote,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(
            &mut self,
            v: &'lt ItemQuoteOrigin,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &'lt ItemQuoteOriginKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &'lt ItemQuoteOriginPosition,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(
            &mut self,
            v: &'lt LoopKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(
            &mut self,
            v: &'lt ControlFlowKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(
            &mut self,
            v: &'lt LoopState,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(
            &mut self,
            v: &'lt ExprKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(
            &mut self,
            v: &'lt GenericParamKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(
            &mut self,
            v: &'lt TraitGoal,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(
            &mut self,
            v: &'lt ImplIdent,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &'lt ProjectionPredicate,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(
            &mut self,
            v: &'lt GenericConstraint,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(
            &mut self,
            v: &'lt GenericParam,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generic_param(self, v)
        }
        fn visit_generics(
            &mut self,
            v: &'lt Generics,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_generics(self, v)
        }
        fn visit_safety_kind(
            &mut self,
            v: &'lt SafetyKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(
            &mut self,
            v: &'lt Attribute,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(
            &mut self,
            v: &'lt AttributeKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(
            &mut self,
            v: &'lt DocCommentKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(
            &mut self,
            v: &'lt SpannedTy,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_spanned_ty(self, v)
        }
        fn visit_param(
            &mut self,
            v: &'lt Param,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_param(self, v)
        }
        fn visit_variant(
            &mut self,
            v: &'lt Variant,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_variant(self, v)
        }
        fn visit_item_kind(
            &mut self,
            v: &'lt ItemKind,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item_kind(self, v)
        }
        fn visit_item(
            &mut self,
            v: &'lt Item,
        ) -> std::ops::ControlFlow<Self::Error, <Self as Monoid>::T> {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericValue::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericValue::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericValue::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Int { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Float { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::App { head, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Arrow { inputs, output } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in inputs {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item)?);
                }
                V::append(&mut visitor_reduce_value, visitor.visit_ty(output)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(inner)?;
                V::append(&mut visitor_reduce_value, visitor.visit_region(region)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Param { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::Slice(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Array { ty, length } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_expr(length.deref())?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::RawPointer { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::AssociatedType { impl_, item } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Opaque { .. } => std::ops::ControlFlow::Continue(V::identity()),
            TyKind::Dyn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_dyn_trait_goal(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in non_self_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Metadata { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_guard_kind(kind)?;
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            BorrowKind::Shared { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BorrowKind::Unique { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BorrowKind::Mut { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            BindingMode::ByValue { .. } => std::ops::ControlFlow::Continue(V::identity()),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            PatKind::Wild { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PatKind::Ascription { pat, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_spanned_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Or { sub_pats } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in sub_pats {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Array { args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Deref { sub_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(sub_pat)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Constant { .. } => std::ops::ControlFlow::Continue(V::identity()),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_binding_mode(mode)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_pat(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Lhs::LocalVar { var, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::ArbitraryExpr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0.deref())?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::FieldAccessor { e, ty, field } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            Lhs::ArrayAccessor { e, ty, index } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref())?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(index)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref())?;
                V::append(&mut visitor_reduce_value, visitor.visit_trait_goal(goal)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplExprKind::Self_ { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::LocalBound { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Parent { impl_, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::Projection { impl_, item, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::ImplApp { impl_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplExprKind::Dyn { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ImplExprKind::Builtin(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics)?);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_impl_item_kind(kind)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplItemKind::Type { ty, parent_bounds } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0)?,
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ImplItemKind::Fn { body, params } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_trait_item_kind(kind)?,
                );
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitItemKind::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_ident(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TraitItemKind::Fn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            TraitItemKind::Default { params, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            QuoteContent::Verbatim { .. } => std::ops::ControlFlow::Continue(V::identity()),
            QuoteContent::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            QuoteContent::Pattern(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            QuoteContent::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Quote(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_quote_content(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin_position(position)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOriginKind::Fn { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::TyAlias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Type { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::MacroInvocation { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
            ItemQuoteOriginKind::Trait { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Impl { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Alias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Use { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::Quote { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::HaxError { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginKind::NotImplementedYet { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemQuoteOriginPosition::Before { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
            ItemQuoteOriginPosition::After { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemQuoteOriginPosition::Replace { .. } => {
                std::ops::ControlFlow::Continue(V::identity())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            LoopKind::UnconditionalLoop { .. } => std::ops::ControlFlow::Continue(V::identity()),
            LoopKind::WhileLoop { condition } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            LoopKind::ForLoop { pat, iterator } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(iterator)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            LoopKind::ForIndexLoop {
                start,
                end,
                var,
                var_ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(start)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(end)?);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(var_ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(init)?;
                V::append(&mut visitor_reduce_value, visitor.visit_pat(body_pat)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(then)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(head)?;
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                for visitor_item in generic_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                for visitor_item in bounds_impls {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Literal { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Array(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_expr(visitor_item_1)?,
                        );
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Match { scrutinee, arms } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(scrutinee)?;
                for visitor_item in arms {
                    V::append(&mut visitor_reduce_value, visitor.visit_arm(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Borrow { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::AddressOf { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Deref(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Let { lhs, rhs, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs)?);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::GlobalId { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::LocalId { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Ascription { e, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(e)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Assign { lhs, value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(lhs)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(value)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                V::append(&mut visitor_reduce_value, visitor.visit_loop_kind(kind)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Break { value, label } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Return { value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Continue { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item)?);
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                for visitor_item in captures {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item)?);
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Block { body, safety_mode } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety_mode)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Quote { contents } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(contents)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericParamKind::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericParamKind::Type { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            TraitGoal { trait_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(goal)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ProjectionPredicate {
                impl_,
                assoc_item,
                ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericConstraint::Lifetime { .. } => std::ops::ControlFlow::Continue(V::identity()),
            GenericConstraint::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_ident(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            GenericConstraint::Projection(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_generic_param_kind(kind)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Generics {
                params,
                constraints,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_param(visitor_item)?,
                    );
                }
                for visitor_item in constraints {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_constraint(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(V::identity()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_attribute_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            AttributeKind::Tool { .. } => std::ops::ControlFlow::Continue(V::identity()),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(V::identity()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Param {
                pat,
                ty,
                ty_span,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item_1)?);
                        ();
                    };
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body)?);
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_param(visitor_item)?,
                    );
                }
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::TyAlias { name, generics, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                for visitor_item in variants {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_variant(visitor_item)?,
                    );
                }
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Trait {
                name,
                generics,
                items,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_trait_item(visitor_item)?,
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics)?;
                V::append(&mut visitor_reduce_value, visitor.visit_ty(self_ty)?);
                {
                    let (visitor_item_0, visitor_item_1) = of_trait;
                    ();
                    for visitor_item in visitor_item_1 {
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_generic_value(visitor_item)?,
                        );
                    }
                };
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_item(visitor_item)?,
                    );
                }
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0)?,
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1)?,
                        );
                    };
                }
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Alias { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::Use { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::Quote { quote, origin } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(quote)?;
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin(origin)?,
                );
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(V::identity()),
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(V::identity()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: VisitorReduceCf<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, <V as Monoid>::T> {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_kind(kind)?;
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta)?);
                std::ops::ControlFlow::Continue(visitor_reduce_value)
            }
        }
    }
}
mod visitor_cf {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST. Each visiting function may break control flow."]
    pub trait VisitorCf<'lt>: Sized {
        type Error;
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
    pub fn visit_generic_value<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_primitive_ty<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            PrimitiveTy::Bool { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Int { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Float { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Char { .. } => std::ops::ControlFlow::Continue(()),
            PrimitiveTy::Str { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Region { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_ty_kind<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
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
            TyKind::Param { .. } => std::ops::ControlFlow::Continue(()),
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
                std::ops::ControlFlow::Continue(())
            }
            TyKind::Opaque { .. } => std::ops::ControlFlow::Continue(()),
            TyKind::Dyn(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_dyn_trait_goal(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
            TyKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                for visitor_item in non_self_args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Metadata { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_pat<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_arm<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_guard<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_borrow_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_binding_mode<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_pat_kind<'lt, V: VisitorCf<'lt>>(
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
            PatKind::Constant { .. } => std::ops::ControlFlow::Continue(()),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                visitor.visit_binding_mode(mode)?;
                std::ops::ControlFlow::Continue(())
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        visitor.visit_pat(visitor_item_1)?;
                    };
                }
                std::ops::ControlFlow::Continue(())
            }
            PatKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_lhs<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Lhs::LocalVar { var, ty } => {
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
    pub fn visit_impl_expr<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_impl_expr_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_impl_item<'lt, V: VisitorCf<'lt>>(
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
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: VisitorCf<'lt>>(
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: VisitorCf<'lt>>(
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
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: VisitorCf<'lt>>(
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
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_quote<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_item_quote_origin<'lt, V: VisitorCf<'lt>>(
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
                visitor.visit_item_quote_origin_position(position)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_item_quote_origin_position<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_loop_kind<'lt, V: VisitorCf<'lt>>(
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
                visitor.visit_ty(var_ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            ControlFlowKind::BreakOnly { .. } => std::ops::ControlFlow::Continue(()),
            ControlFlowKind::BreakOrReturn { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_expr_kind<'lt, V: VisitorCf<'lt>>(
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
            ExprKind::Literal { .. } => std::ops::ControlFlow::Continue(()),
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
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
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
            ExprKind::GlobalId { .. } => std::ops::ControlFlow::Continue(()),
            ExprKind::LocalId { .. } => std::ops::ControlFlow::Continue(()),
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
            ExprKind::Error { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_trait_goal<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            TraitGoal { trait_, args } => {
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item)?;
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_projection_predicate<'lt, V: VisitorCf<'lt>>(
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
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_generic_param<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_metadata(meta)?;
                visitor.visit_generic_param_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_safety_kind<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SafetyKind::Safe { .. } => std::ops::ControlFlow::Continue(()),
            SafetyKind::Unsafe { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_doc_comment_kind<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            DocCommentKind::Line { .. } => std::ops::ControlFlow::Continue(()),
            DocCommentKind::Block { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_ty(ty)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: VisitorCf<'lt>>(
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
    pub fn visit_variant<'lt, V: VisitorCf<'lt>>(
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
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        visitor.visit_ty(visitor_item_1)?;
                        ();
                    };
                }
                std::ops::ControlFlow::Continue(())
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: VisitorCf<'lt>>(
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
                visitor.visit_generics(generics)?;
                visitor.visit_expr(body)?;
                for visitor_item in params {
                    visitor.visit_param(visitor_item)?;
                }
                visitor.visit_safety_kind(safety)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::TyAlias { name, generics, ty } => {
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
                    ();
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
            ItemKind::Alias { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Use { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::Quote { quote, origin } => {
                visitor.visit_quote(quote)?;
                visitor.visit_item_quote_origin(origin)?;
                std::ops::ControlFlow::Continue(())
            }
            ItemKind::Error { .. } => std::ops::ControlFlow::Continue(()),
            ItemKind::NotImplementedYet { .. } => std::ops::ControlFlow::Continue(()),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: VisitorCf<'lt>>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> std::ops::ControlFlow<V::Error, ()> {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_item_kind(kind)?;
                visitor.visit_metadata(meta)?;
                std::ops::ControlFlow::Continue(())
            }
        }
    }
}
mod visitor_map_reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait VisitorMapReduce: Sized + Monoid {
        fn visit_generic_value(&mut self, v: &mut GenericValue) -> <Self as Monoid>::T {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &mut PrimitiveTy) -> <Self as Monoid>::T {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &mut Region) -> <Self as Monoid>::T {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &mut Ty) -> <Self as Monoid>::T {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &mut TyKind) -> <Self as Monoid>::T {
            visit_ty_kind(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &mut DynTraitGoal) -> <Self as Monoid>::T {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &mut Metadata) -> <Self as Monoid>::T {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &mut Expr) -> <Self as Monoid>::T {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &mut Pat) -> <Self as Monoid>::T {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &mut Arm) -> <Self as Monoid>::T {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &mut Guard) -> <Self as Monoid>::T {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &mut BorrowKind) -> <Self as Monoid>::T {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &mut BindingMode) -> <Self as Monoid>::T {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &mut PatKind) -> <Self as Monoid>::T {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &mut GuardKind) -> <Self as Monoid>::T {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &mut Lhs) -> <Self as Monoid>::T {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &mut ImplExpr) -> <Self as Monoid>::T {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &mut ImplExprKind) -> <Self as Monoid>::T {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &mut ImplItem) -> <Self as Monoid>::T {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &mut ImplItemKind) -> <Self as Monoid>::T {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &mut TraitItem) -> <Self as Monoid>::T {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &mut TraitItemKind) -> <Self as Monoid>::T {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &mut QuoteContent) -> <Self as Monoid>::T {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &mut Quote) -> <Self as Monoid>::T {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &mut ItemQuoteOrigin) -> <Self as Monoid>::T {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &mut ItemQuoteOriginKind,
        ) -> <Self as Monoid>::T {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &mut ItemQuoteOriginPosition,
        ) -> <Self as Monoid>::T {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &mut LoopKind) -> <Self as Monoid>::T {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &mut ControlFlowKind) -> <Self as Monoid>::T {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &mut LoopState) -> <Self as Monoid>::T {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &mut ExprKind) -> <Self as Monoid>::T {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &mut GenericParamKind) -> <Self as Monoid>::T {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &mut TraitGoal) -> <Self as Monoid>::T {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &mut ImplIdent) -> <Self as Monoid>::T {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &mut ProjectionPredicate,
        ) -> <Self as Monoid>::T {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &mut GenericConstraint) -> <Self as Monoid>::T {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &mut GenericParam) -> <Self as Monoid>::T {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &mut Generics) -> <Self as Monoid>::T {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &mut SafetyKind) -> <Self as Monoid>::T {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &mut Attribute) -> <Self as Monoid>::T {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &mut AttributeKind) -> <Self as Monoid>::T {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &mut DocCommentKind) -> <Self as Monoid>::T {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &mut SpannedTy) -> <Self as Monoid>::T {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &mut Param) -> <Self as Monoid>::T {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &mut Variant) -> <Self as Monoid>::T {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &mut ItemKind) -> <Self as Monoid>::T {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &mut Item) -> <Self as Monoid>::T {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_generic_value<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut GenericValue,
    ) -> <V as Monoid>::T {
        match v {
            GenericValue::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            GenericValue::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            GenericValue::Lifetime { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut PrimitiveTy,
    ) -> <V as Monoid>::T {
        match v {
            PrimitiveTy::Bool { .. } => V::identity(),
            PrimitiveTy::Int { .. } => V::identity(),
            PrimitiveTy::Float { .. } => V::identity(),
            PrimitiveTy::Char { .. } => V::identity(),
            PrimitiveTy::Str { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_region<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Region,
    ) -> <V as Monoid>::T {
        match v {
            Region { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: VisitorMapReduce + Monoid>(visitor: &mut V, v: &mut Ty) -> <V as Monoid>::T {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref_mut());
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut TyKind,
    ) -> <V as Monoid>::T {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
                visitor_reduce_value
            }
            TyKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item));
                }
                visitor_reduce_value
            }
            TyKind::App { head, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TyKind::Arrow { inputs, output } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in inputs {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_ty(output));
                visitor_reduce_value
            }
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(inner);
                V::append(&mut visitor_reduce_value, visitor.visit_region(region));
                visitor_reduce_value
            }
            TyKind::Param { .. } => V::identity(),
            TyKind::Slice(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            TyKind::Array { ty, length } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_expr(length.deref_mut()),
                );
                visitor_reduce_value
            }
            TyKind::RawPointer { .. } => V::identity(),
            TyKind::AssociatedType { impl_, item } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                visitor_reduce_value
            }
            TyKind::Opaque { .. } => V::identity(),
            TyKind::Dyn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_dyn_trait_goal(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TyKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut DynTraitGoal,
    ) -> <V as Monoid>::T {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in non_self_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Metadata,
    ) -> <V as Monoid>::T {
        match v {
            Metadata { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Expr,
    ) -> <V as Monoid>::T {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref_mut());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Pat,
    ) -> <V as Monoid>::T {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref_mut());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Arm,
    ) -> <V as Monoid>::T {
        match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_guard<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Guard,
    ) -> <V as Monoid>::T {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut BorrowKind,
    ) -> <V as Monoid>::T {
        match v {
            BorrowKind::Shared { .. } => V::identity(),
            BorrowKind::Unique { .. } => V::identity(),
            BorrowKind::Mut { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut BindingMode,
    ) -> <V as Monoid>::T {
        match v {
            BindingMode::ByValue { .. } => V::identity(),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut PatKind,
    ) -> <V as Monoid>::T {
        match v {
            PatKind::Wild { .. } => V::identity(),
            PatKind::Ascription { pat, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_spanned_ty(ty));
                visitor_reduce_value
            }
            PatKind::Or { sub_pats } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in sub_pats {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                visitor_reduce_value
            }
            PatKind::Array { args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                visitor_reduce_value
            }
            PatKind::Deref { sub_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(sub_pat);
                visitor_reduce_value
            }
            PatKind::Constant { .. } => V::identity(),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_binding_mode(mode);
                visitor_reduce_value
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item_1));
                    };
                }
                visitor_reduce_value
            }
            PatKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut GuardKind,
    ) -> <V as Monoid>::T {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Lhs,
    ) -> <V as Monoid>::T {
        match v {
            Lhs::LocalVar { var, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
            Lhs::ArbitraryExpr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0.deref_mut());
                visitor_reduce_value
            }
            Lhs::FieldAccessor { e, ty, field } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref_mut());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            Lhs::ArrayAccessor { e, ty, index } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref_mut());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_expr(index));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ImplExpr,
    ) -> <V as Monoid>::T {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref_mut());
                V::append(&mut visitor_reduce_value, visitor.visit_trait_goal(goal));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ImplExprKind,
    ) -> <V as Monoid>::T {
        match v {
            ImplExprKind::Self_ { .. } => V::identity(),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                visitor_reduce_value
            }
            ImplExprKind::LocalBound { .. } => V::identity(),
            ImplExprKind::Parent { impl_, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident));
                visitor_reduce_value
            }
            ImplExprKind::Projection { impl_, item, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident));
                visitor_reduce_value
            }
            ImplExprKind::ImplApp { impl_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ImplExprKind::Dyn { .. } => V::identity(),
            ImplExprKind::Builtin(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ImplItem,
    ) -> <V as Monoid>::T {
        match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics));
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_impl_item_kind(kind),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ImplItemKind,
    ) -> <V as Monoid>::T {
        match v {
            ImplItemKind::Type { ty, parent_bounds } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0),
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1),
                        );
                    };
                }
                visitor_reduce_value
            }
            ImplItemKind::Fn { body, params } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut TraitItem,
    ) -> <V as Monoid>::T {
        match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_trait_item_kind(kind),
                );
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut TraitItemKind,
    ) -> <V as Monoid>::T {
        match v {
            TraitItemKind::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_ident(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TraitItemKind::Fn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            TraitItemKind::Default { params, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut QuoteContent,
    ) -> <V as Monoid>::T {
        match v {
            QuoteContent::Verbatim { .. } => V::identity(),
            QuoteContent::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            QuoteContent::Pattern(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(anon_field_0);
                visitor_reduce_value
            }
            QuoteContent::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Quote,
    ) -> <V as Monoid>::T {
        match v {
            Quote(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_quote_content(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOrigin,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin_position(position),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginKind,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOriginKind::Fn { .. } => V::identity(),
            ItemQuoteOriginKind::TyAlias { .. } => V::identity(),
            ItemQuoteOriginKind::Type { .. } => V::identity(),
            ItemQuoteOriginKind::MacroInvocation { .. } => V::identity(),
            ItemQuoteOriginKind::Trait { .. } => V::identity(),
            ItemQuoteOriginKind::Impl { .. } => V::identity(),
            ItemQuoteOriginKind::Alias { .. } => V::identity(),
            ItemQuoteOriginKind::Use { .. } => V::identity(),
            ItemQuoteOriginKind::Quote { .. } => V::identity(),
            ItemQuoteOriginKind::HaxError { .. } => V::identity(),
            ItemQuoteOriginKind::NotImplementedYet { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ItemQuoteOriginPosition,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOriginPosition::Before { .. } => V::identity(),
            ItemQuoteOriginPosition::After { .. } => V::identity(),
            ItemQuoteOriginPosition::Replace { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut LoopKind,
    ) -> <V as Monoid>::T {
        match v {
            LoopKind::UnconditionalLoop { .. } => V::identity(),
            LoopKind::WhileLoop { condition } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition);
                visitor_reduce_value
            }
            LoopKind::ForLoop { pat, iterator } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(iterator));
                visitor_reduce_value
            }
            LoopKind::ForIndexLoop {
                start,
                end,
                var,
                var_ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(start);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(end));
                V::append(&mut visitor_reduce_value, visitor.visit_ty(var_ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ControlFlowKind,
    ) -> <V as Monoid>::T {
        match v {
            ControlFlowKind::BreakOnly { .. } => V::identity(),
            ControlFlowKind::BreakOrReturn { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut LoopState,
    ) -> <V as Monoid>::T {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(init);
                V::append(&mut visitor_reduce_value, visitor.visit_pat(body_pat));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ExprKind,
    ) -> <V as Monoid>::T {
        match v {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(then));
                visitor_reduce_value
            }
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(head);
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                for visitor_item in generic_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                for visitor_item in bounds_impls {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ExprKind::Literal { .. } => V::identity(),
            ExprKind::Array(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_expr(visitor_item_1),
                        );
                    };
                }
                visitor_reduce_value
            }
            ExprKind::Match { scrutinee, arms } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(scrutinee);
                for visitor_item in arms {
                    V::append(&mut visitor_reduce_value, visitor.visit_arm(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Borrow { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner);
                visitor_reduce_value
            }
            ExprKind::AddressOf { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner);
                visitor_reduce_value
            }
            ExprKind::Deref(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            ExprKind::Let { lhs, rhs, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs));
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                visitor_reduce_value
            }
            ExprKind::GlobalId { .. } => V::identity(),
            ExprKind::LocalId { .. } => V::identity(),
            ExprKind::Ascription { e, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(e);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            ExprKind::Assign { lhs, value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(value));
                visitor_reduce_value
            }
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                V::append(&mut visitor_reduce_value, visitor.visit_loop_kind(kind));
                visitor_reduce_value
            }
            ExprKind::Break { value, label } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value);
                visitor_reduce_value
            }
            ExprKind::Return { value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value);
                visitor_reduce_value
            }
            ExprKind::Continue { .. } => V::identity(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                for visitor_item in captures {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Block { body, safety_mode } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety_mode),
                );
                visitor_reduce_value
            }
            ExprKind::Quote { contents } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(contents);
                visitor_reduce_value
            }
            ExprKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut GenericParamKind,
    ) -> <V as Monoid>::T {
        match v {
            GenericParamKind::Lifetime { .. } => V::identity(),
            GenericParamKind::Type { .. } => V::identity(),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut TraitGoal,
    ) -> <V as Monoid>::T {
        match v {
            TraitGoal { trait_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ImplIdent,
    ) -> <V as Monoid>::T {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(goal);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ProjectionPredicate,
    ) -> <V as Monoid>::T {
        match v {
            ProjectionPredicate {
                impl_,
                assoc_item,
                ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut GenericConstraint,
    ) -> <V as Monoid>::T {
        match v {
            GenericConstraint::Lifetime { .. } => V::identity(),
            GenericConstraint::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_ident(anon_field_0);
                visitor_reduce_value
            }
            GenericConstraint::Projection(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut GenericParam,
    ) -> <V as Monoid>::T {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_generic_param_kind(kind),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Generics,
    ) -> <V as Monoid>::T {
        match v {
            Generics {
                params,
                constraints,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_param(visitor_item),
                    );
                }
                for visitor_item in constraints {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_constraint(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut SafetyKind,
    ) -> <V as Monoid>::T {
        match v {
            SafetyKind::Safe { .. } => V::identity(),
            SafetyKind::Unsafe { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Attribute,
    ) -> <V as Monoid>::T {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_attribute_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut AttributeKind,
    ) -> <V as Monoid>::T {
        match v {
            AttributeKind::Tool { .. } => V::identity(),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut DocCommentKind,
    ) -> <V as Monoid>::T {
        match v {
            DocCommentKind::Line { .. } => V::identity(),
            DocCommentKind::Block { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut SpannedTy,
    ) -> <V as Monoid>::T {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Param,
    ) -> <V as Monoid>::T {
        match v {
            Param {
                pat,
                ty,
                ty_span,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_variant<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Variant,
    ) -> <V as Monoid>::T {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item_1));
                        ();
                    };
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut ItemKind,
    ) -> <V as Monoid>::T {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_safety_kind(safety));
                visitor_reduce_value
            }
            ItemKind::TyAlias { name, generics, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                for visitor_item in variants {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_variant(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ItemKind::Trait {
                name,
                generics,
                items,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_trait_item(visitor_item),
                    );
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(self_ty));
                {
                    let (visitor_item_0, visitor_item_1) = of_trait;
                    ();
                    for visitor_item in visitor_item_1 {
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_generic_value(visitor_item),
                        );
                    }
                };
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_item(visitor_item),
                    );
                }
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0),
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1),
                        );
                    };
                }
                V::append(&mut visitor_reduce_value, visitor.visit_safety_kind(safety));
                visitor_reduce_value
            }
            ItemKind::Alias { .. } => V::identity(),
            ItemKind::Use { .. } => V::identity(),
            ItemKind::Quote { quote, origin } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(quote);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin(origin),
                );
                visitor_reduce_value
            }
            ItemKind::Error { .. } => V::identity(),
            ItemKind::NotImplementedYet { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: VisitorMapReduce + Monoid>(
        visitor: &mut V,
        v: &mut Item,
    ) -> <V as Monoid>::T {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_kind(kind);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
}
mod visitor_map {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits mutable nodes of each type of the AST."]
    pub trait VisitorMap: Sized {
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
    pub fn visit_generic_value<V: VisitorMap>(visitor: &mut V, v: &mut GenericValue) -> () {
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
    pub fn visit_primitive_ty<V: VisitorMap>(visitor: &mut V, v: &mut PrimitiveTy) -> () {
        match v {
            PrimitiveTy::Bool { .. } => (),
            PrimitiveTy::Int { .. } => (),
            PrimitiveTy::Float { .. } => (),
            PrimitiveTy::Char { .. } => (),
            PrimitiveTy::Str { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_region<V: VisitorMap>(visitor: &mut V, v: &mut Region) -> () {
        match v {
            Region { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<V: VisitorMap>(visitor: &mut V, v: &mut Ty) -> () {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref_mut());
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<V: VisitorMap>(visitor: &mut V, v: &mut TyKind) -> () {
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
            TyKind::Param { .. } => (),
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
                ()
            }
            TyKind::Opaque { .. } => (),
            TyKind::Dyn(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_dyn_trait_goal(visitor_item);
                }
                ()
            }
            TyKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<V: VisitorMap>(visitor: &mut V, v: &mut DynTraitGoal) -> () {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                for visitor_item in non_self_args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<V: VisitorMap>(visitor: &mut V, v: &mut Metadata) -> () {
        match v {
            Metadata { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<V: VisitorMap>(visitor: &mut V, v: &mut Expr) -> () {
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
    pub fn visit_pat<V: VisitorMap>(visitor: &mut V, v: &mut Pat) -> () {
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
    pub fn visit_arm<V: VisitorMap>(visitor: &mut V, v: &mut Arm) -> () {
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
    pub fn visit_guard<V: VisitorMap>(visitor: &mut V, v: &mut Guard) -> () {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<V: VisitorMap>(visitor: &mut V, v: &mut BorrowKind) -> () {
        match v {
            BorrowKind::Shared { .. } => (),
            BorrowKind::Unique { .. } => (),
            BorrowKind::Mut { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<V: VisitorMap>(visitor: &mut V, v: &mut BindingMode) -> () {
        match v {
            BindingMode::ByValue { .. } => (),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<V: VisitorMap>(visitor: &mut V, v: &mut PatKind) -> () {
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
            PatKind::Constant { .. } => (),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                visitor.visit_binding_mode(mode);
                ()
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        visitor.visit_pat(visitor_item_1);
                    };
                }
                ()
            }
            PatKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<V: VisitorMap>(visitor: &mut V, v: &mut GuardKind) -> () {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs);
                visitor.visit_expr(rhs);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<V: VisitorMap>(visitor: &mut V, v: &mut Lhs) -> () {
        match v {
            Lhs::LocalVar { var, ty } => {
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
    pub fn visit_impl_expr<V: VisitorMap>(visitor: &mut V, v: &mut ImplExpr) -> () {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref_mut());
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<V: VisitorMap>(visitor: &mut V, v: &mut ImplExprKind) -> () {
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
    pub fn visit_impl_item<V: VisitorMap>(visitor: &mut V, v: &mut ImplItem) -> () {
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
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<V: VisitorMap>(visitor: &mut V, v: &mut ImplItemKind) -> () {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<V: VisitorMap>(visitor: &mut V, v: &mut TraitItem) -> () {
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
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<V: VisitorMap>(visitor: &mut V, v: &mut TraitItemKind) -> () {
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
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<V: VisitorMap>(visitor: &mut V, v: &mut QuoteContent) -> () {
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
    pub fn visit_quote<V: VisitorMap>(visitor: &mut V, v: &mut Quote) -> () {
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
    pub fn visit_item_quote_origin<V: VisitorMap>(visitor: &mut V, v: &mut ItemQuoteOrigin) -> () {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                visitor.visit_item_quote_origin_kind(item_kind);
                visitor.visit_item_quote_origin_position(position);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<V: VisitorMap>(
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
    pub fn visit_item_quote_origin_position<V: VisitorMap>(
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
    pub fn visit_loop_kind<V: VisitorMap>(visitor: &mut V, v: &mut LoopKind) -> () {
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
                visitor.visit_ty(var_ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<V: VisitorMap>(visitor: &mut V, v: &mut ControlFlowKind) -> () {
        match v {
            ControlFlowKind::BreakOnly { .. } => (),
            ControlFlowKind::BreakOrReturn { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<V: VisitorMap>(visitor: &mut V, v: &mut LoopState) -> () {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init);
                visitor.visit_pat(body_pat);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<V: VisitorMap>(visitor: &mut V, v: &mut ExprKind) -> () {
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
            ExprKind::Literal { .. } => (),
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
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
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
            ExprKind::GlobalId { .. } => (),
            ExprKind::LocalId { .. } => (),
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
            ExprKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<V: VisitorMap>(
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
    pub fn visit_trait_goal<V: VisitorMap>(visitor: &mut V, v: &mut TraitGoal) -> () {
        match v {
            TraitGoal { trait_, args } => {
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<V: VisitorMap>(visitor: &mut V, v: &mut ImplIdent) -> () {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<V: VisitorMap>(
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
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<V: VisitorMap>(
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
    pub fn visit_generic_param<V: VisitorMap>(visitor: &mut V, v: &mut GenericParam) -> () {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<V: VisitorMap>(visitor: &mut V, v: &mut Generics) -> () {
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
    pub fn visit_safety_kind<V: VisitorMap>(visitor: &mut V, v: &mut SafetyKind) -> () {
        match v {
            SafetyKind::Safe { .. } => (),
            SafetyKind::Unsafe { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<V: VisitorMap>(visitor: &mut V, v: &mut Attribute) -> () {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<V: VisitorMap>(visitor: &mut V, v: &mut AttributeKind) -> () {
        match v {
            AttributeKind::Tool { .. } => (),
            AttributeKind::DocComment { kind, body } => {
                visitor.visit_doc_comment_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<V: VisitorMap>(visitor: &mut V, v: &mut DocCommentKind) -> () {
        match v {
            DocCommentKind::Line { .. } => (),
            DocCommentKind::Block { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<V: VisitorMap>(visitor: &mut V, v: &mut SpannedTy) -> () {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<V: VisitorMap>(visitor: &mut V, v: &mut Param) -> () {
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
    pub fn visit_variant<V: VisitorMap>(visitor: &mut V, v: &mut Variant) -> () {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        visitor.visit_ty(visitor_item_1);
                        ();
                    };
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<V: VisitorMap>(visitor: &mut V, v: &mut ItemKind) -> () {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                visitor.visit_generics(generics);
                visitor.visit_expr(body);
                for visitor_item in params {
                    visitor.visit_param(visitor_item);
                }
                visitor.visit_safety_kind(safety);
                ()
            }
            ItemKind::TyAlias { name, generics, ty } => {
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
                    ();
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
            ItemKind::Alias { .. } => (),
            ItemKind::Use { .. } => (),
            ItemKind::Quote { quote, origin } => {
                visitor.visit_quote(quote);
                visitor.visit_item_quote_origin(origin);
                ()
            }
            ItemKind::Error { .. } => (),
            ItemKind::NotImplementedYet { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_item<V: VisitorMap>(visitor: &mut V, v: &mut Item) -> () {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
}
mod visitor_reduce {
    use super::*;
    #[doc = "Map visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait VisitorReduce<'lt>: Sized + Monoid {
        fn visit_generic_value(&mut self, v: &'lt GenericValue) -> <Self as Monoid>::T {
            visit_generic_value(self, v)
        }
        fn visit_primitive_ty(&mut self, v: &'lt PrimitiveTy) -> <Self as Monoid>::T {
            visit_primitive_ty(self, v)
        }
        fn visit_region(&mut self, v: &'lt Region) -> <Self as Monoid>::T {
            visit_region(self, v)
        }
        fn visit_ty(&mut self, v: &'lt Ty) -> <Self as Monoid>::T {
            visit_ty(self, v)
        }
        fn visit_ty_kind(&mut self, v: &'lt TyKind) -> <Self as Monoid>::T {
            visit_ty_kind(self, v)
        }
        fn visit_dyn_trait_goal(&mut self, v: &'lt DynTraitGoal) -> <Self as Monoid>::T {
            visit_dyn_trait_goal(self, v)
        }
        fn visit_metadata(&mut self, v: &'lt Metadata) -> <Self as Monoid>::T {
            visit_metadata(self, v)
        }
        fn visit_expr(&mut self, v: &'lt Expr) -> <Self as Monoid>::T {
            visit_expr(self, v)
        }
        fn visit_pat(&mut self, v: &'lt Pat) -> <Self as Monoid>::T {
            visit_pat(self, v)
        }
        fn visit_arm(&mut self, v: &'lt Arm) -> <Self as Monoid>::T {
            visit_arm(self, v)
        }
        fn visit_guard(&mut self, v: &'lt Guard) -> <Self as Monoid>::T {
            visit_guard(self, v)
        }
        fn visit_borrow_kind(&mut self, v: &'lt BorrowKind) -> <Self as Monoid>::T {
            visit_borrow_kind(self, v)
        }
        fn visit_binding_mode(&mut self, v: &'lt BindingMode) -> <Self as Monoid>::T {
            visit_binding_mode(self, v)
        }
        fn visit_pat_kind(&mut self, v: &'lt PatKind) -> <Self as Monoid>::T {
            visit_pat_kind(self, v)
        }
        fn visit_guard_kind(&mut self, v: &'lt GuardKind) -> <Self as Monoid>::T {
            visit_guard_kind(self, v)
        }
        fn visit_lhs(&mut self, v: &'lt Lhs) -> <Self as Monoid>::T {
            visit_lhs(self, v)
        }
        fn visit_impl_expr(&mut self, v: &'lt ImplExpr) -> <Self as Monoid>::T {
            visit_impl_expr(self, v)
        }
        fn visit_impl_expr_kind(&mut self, v: &'lt ImplExprKind) -> <Self as Monoid>::T {
            visit_impl_expr_kind(self, v)
        }
        fn visit_impl_item(&mut self, v: &'lt ImplItem) -> <Self as Monoid>::T {
            visit_impl_item(self, v)
        }
        fn visit_impl_item_kind(&mut self, v: &'lt ImplItemKind) -> <Self as Monoid>::T {
            visit_impl_item_kind(self, v)
        }
        fn visit_trait_item(&mut self, v: &'lt TraitItem) -> <Self as Monoid>::T {
            visit_trait_item(self, v)
        }
        fn visit_trait_item_kind(&mut self, v: &'lt TraitItemKind) -> <Self as Monoid>::T {
            visit_trait_item_kind(self, v)
        }
        fn visit_quote_content(&mut self, v: &'lt QuoteContent) -> <Self as Monoid>::T {
            visit_quote_content(self, v)
        }
        fn visit_quote(&mut self, v: &'lt Quote) -> <Self as Monoid>::T {
            visit_quote(self, v)
        }
        fn visit_item_quote_origin(&mut self, v: &'lt ItemQuoteOrigin) -> <Self as Monoid>::T {
            visit_item_quote_origin(self, v)
        }
        fn visit_item_quote_origin_kind(
            &mut self,
            v: &'lt ItemQuoteOriginKind,
        ) -> <Self as Monoid>::T {
            visit_item_quote_origin_kind(self, v)
        }
        fn visit_item_quote_origin_position(
            &mut self,
            v: &'lt ItemQuoteOriginPosition,
        ) -> <Self as Monoid>::T {
            visit_item_quote_origin_position(self, v)
        }
        fn visit_loop_kind(&mut self, v: &'lt LoopKind) -> <Self as Monoid>::T {
            visit_loop_kind(self, v)
        }
        fn visit_control_flow_kind(&mut self, v: &'lt ControlFlowKind) -> <Self as Monoid>::T {
            visit_control_flow_kind(self, v)
        }
        fn visit_loop_state(&mut self, v: &'lt LoopState) -> <Self as Monoid>::T {
            visit_loop_state(self, v)
        }
        fn visit_expr_kind(&mut self, v: &'lt ExprKind) -> <Self as Monoid>::T {
            visit_expr_kind(self, v)
        }
        fn visit_generic_param_kind(&mut self, v: &'lt GenericParamKind) -> <Self as Monoid>::T {
            visit_generic_param_kind(self, v)
        }
        fn visit_trait_goal(&mut self, v: &'lt TraitGoal) -> <Self as Monoid>::T {
            visit_trait_goal(self, v)
        }
        fn visit_impl_ident(&mut self, v: &'lt ImplIdent) -> <Self as Monoid>::T {
            visit_impl_ident(self, v)
        }
        fn visit_projection_predicate(
            &mut self,
            v: &'lt ProjectionPredicate,
        ) -> <Self as Monoid>::T {
            visit_projection_predicate(self, v)
        }
        fn visit_generic_constraint(&mut self, v: &'lt GenericConstraint) -> <Self as Monoid>::T {
            visit_generic_constraint(self, v)
        }
        fn visit_generic_param(&mut self, v: &'lt GenericParam) -> <Self as Monoid>::T {
            visit_generic_param(self, v)
        }
        fn visit_generics(&mut self, v: &'lt Generics) -> <Self as Monoid>::T {
            visit_generics(self, v)
        }
        fn visit_safety_kind(&mut self, v: &'lt SafetyKind) -> <Self as Monoid>::T {
            visit_safety_kind(self, v)
        }
        fn visit_attribute(&mut self, v: &'lt Attribute) -> <Self as Monoid>::T {
            visit_attribute(self, v)
        }
        fn visit_attribute_kind(&mut self, v: &'lt AttributeKind) -> <Self as Monoid>::T {
            visit_attribute_kind(self, v)
        }
        fn visit_doc_comment_kind(&mut self, v: &'lt DocCommentKind) -> <Self as Monoid>::T {
            visit_doc_comment_kind(self, v)
        }
        fn visit_spanned_ty(&mut self, v: &'lt SpannedTy) -> <Self as Monoid>::T {
            visit_spanned_ty(self, v)
        }
        fn visit_param(&mut self, v: &'lt Param) -> <Self as Monoid>::T {
            visit_param(self, v)
        }
        fn visit_variant(&mut self, v: &'lt Variant) -> <Self as Monoid>::T {
            visit_variant(self, v)
        }
        fn visit_item_kind(&mut self, v: &'lt ItemKind) -> <Self as Monoid>::T {
            visit_item_kind(self, v)
        }
        fn visit_item(&mut self, v: &'lt Item) -> <Self as Monoid>::T {
            visit_item(self, v)
        }
    }
    #[allow(unused)]
    pub fn visit_generic_value<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericValue,
    ) -> <V as Monoid>::T {
        match v {
            GenericValue::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            GenericValue::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            GenericValue::Lifetime { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_primitive_ty<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt PrimitiveTy,
    ) -> <V as Monoid>::T {
        match v {
            PrimitiveTy::Bool { .. } => V::identity(),
            PrimitiveTy::Int { .. } => V::identity(),
            PrimitiveTy::Float { .. } => V::identity(),
            PrimitiveTy::Char { .. } => V::identity(),
            PrimitiveTy::Str { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Region,
    ) -> <V as Monoid>::T {
        match v {
            Region { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Ty,
    ) -> <V as Monoid>::T {
        match v {
            Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty_kind(anon_field_0.deref());
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TyKind,
    ) -> <V as Monoid>::T {
        match v {
            TyKind::Primitive(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_primitive_ty(anon_field_0);
                visitor_reduce_value
            }
            TyKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item));
                }
                visitor_reduce_value
            }
            TyKind::App { head, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TyKind::Arrow { inputs, output } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in inputs {
                    V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_ty(output));
                visitor_reduce_value
            }
            TyKind::Ref {
                inner,
                mutable,
                region,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(inner);
                V::append(&mut visitor_reduce_value, visitor.visit_region(region));
                visitor_reduce_value
            }
            TyKind::Param { .. } => V::identity(),
            TyKind::Slice(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            TyKind::Array { ty, length } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_expr(length.deref()),
                );
                visitor_reduce_value
            }
            TyKind::RawPointer { .. } => V::identity(),
            TyKind::AssociatedType { impl_, item } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                visitor_reduce_value
            }
            TyKind::Opaque { .. } => V::identity(),
            TyKind::Dyn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_dyn_trait_goal(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TyKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt DynTraitGoal,
    ) -> <V as Monoid>::T {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in non_self_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Metadata,
    ) -> <V as Monoid>::T {
        match v {
            Metadata { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Expr,
    ) -> <V as Monoid>::T {
        match v {
            Expr { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr_kind(kind.deref());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Pat,
    ) -> <V as Monoid>::T {
        match v {
            Pat { kind, ty, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat_kind(kind.deref());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_arm<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Arm,
    ) -> <V as Monoid>::T {
        match v {
            Arm {
                pat,
                body,
                guard,
                meta,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_guard<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Guard,
    ) -> <V as Monoid>::T {
        match v {
            Guard { kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_guard_kind(kind);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt BorrowKind,
    ) -> <V as Monoid>::T {
        match v {
            BorrowKind::Shared { .. } => V::identity(),
            BorrowKind::Unique { .. } => V::identity(),
            BorrowKind::Mut { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt BindingMode,
    ) -> <V as Monoid>::T {
        match v {
            BindingMode::ByValue { .. } => V::identity(),
            BindingMode::ByRef(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_borrow_kind(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt PatKind,
    ) -> <V as Monoid>::T {
        match v {
            PatKind::Wild { .. } => V::identity(),
            PatKind::Ascription { pat, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_spanned_ty(ty));
                visitor_reduce_value
            }
            PatKind::Or { sub_pats } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in sub_pats {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                visitor_reduce_value
            }
            PatKind::Array { args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                visitor_reduce_value
            }
            PatKind::Deref { sub_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(sub_pat);
                visitor_reduce_value
            }
            PatKind::Constant { .. } => V::identity(),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_binding_mode(mode);
                visitor_reduce_value
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item_1));
                    };
                }
                visitor_reduce_value
            }
            PatKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GuardKind,
    ) -> <V as Monoid>::T {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Lhs,
    ) -> <V as Monoid>::T {
        match v {
            Lhs::LocalVar { var, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
            Lhs::ArbitraryExpr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0.deref());
                visitor_reduce_value
            }
            Lhs::FieldAccessor { e, ty, field } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            Lhs::ArrayAccessor { e, ty, index } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(e.deref());
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                V::append(&mut visitor_reduce_value, visitor.visit_expr(index));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplExpr,
    ) -> <V as Monoid>::T {
        match v {
            ImplExpr { kind, goal } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr_kind(kind.deref());
                V::append(&mut visitor_reduce_value, visitor.visit_trait_goal(goal));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplExprKind,
    ) -> <V as Monoid>::T {
        match v {
            ImplExprKind::Self_ { .. } => V::identity(),
            ImplExprKind::Concrete(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                visitor_reduce_value
            }
            ImplExprKind::LocalBound { .. } => V::identity(),
            ImplExprKind::Parent { impl_, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident));
                visitor_reduce_value
            }
            ImplExprKind::Projection { impl_, item, ident } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_impl_ident(ident));
                visitor_reduce_value
            }
            ImplExprKind::ImplApp { impl_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ImplExprKind::Dyn { .. } => V::identity(),
            ImplExprKind::Builtin(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplItem,
    ) -> <V as Monoid>::T {
        match v {
            ImplItem {
                meta,
                generics,
                kind,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics));
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_impl_item_kind(kind),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplItemKind,
    ) -> <V as Monoid>::T {
        match v {
            ImplItemKind::Type { ty, parent_bounds } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0),
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1),
                        );
                    };
                }
                visitor_reduce_value
            }
            ImplItemKind::Fn { body, params } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitItem,
    ) -> <V as Monoid>::T {
        match v {
            TraitItem {
                meta,
                kind,
                generics,
                ident,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_trait_item_kind(kind),
                );
                V::append(&mut visitor_reduce_value, visitor.visit_generics(generics));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitItemKind,
    ) -> <V as Monoid>::T {
        match v {
            TraitItemKind::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_ident(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            TraitItemKind::Fn(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
            TraitItemKind::Default { params, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt QuoteContent,
    ) -> <V as Monoid>::T {
        match v {
            QuoteContent::Verbatim { .. } => V::identity(),
            QuoteContent::Expr(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            QuoteContent::Pattern(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(anon_field_0);
                visitor_reduce_value
            }
            QuoteContent::Ty(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_quote<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Quote,
    ) -> <V as Monoid>::T {
        match v {
            Quote(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_quote_content(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOrigin,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOrigin {
                item_kind,
                item_ident,
                position,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_quote_origin_kind(item_kind);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin_position(position),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginKind,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOriginKind::Fn { .. } => V::identity(),
            ItemQuoteOriginKind::TyAlias { .. } => V::identity(),
            ItemQuoteOriginKind::Type { .. } => V::identity(),
            ItemQuoteOriginKind::MacroInvocation { .. } => V::identity(),
            ItemQuoteOriginKind::Trait { .. } => V::identity(),
            ItemQuoteOriginKind::Impl { .. } => V::identity(),
            ItemQuoteOriginKind::Alias { .. } => V::identity(),
            ItemQuoteOriginKind::Use { .. } => V::identity(),
            ItemQuoteOriginKind::Quote { .. } => V::identity(),
            ItemQuoteOriginKind::HaxError { .. } => V::identity(),
            ItemQuoteOriginKind::NotImplementedYet { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_position<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemQuoteOriginPosition,
    ) -> <V as Monoid>::T {
        match v {
            ItemQuoteOriginPosition::Before { .. } => V::identity(),
            ItemQuoteOriginPosition::After { .. } => V::identity(),
            ItemQuoteOriginPosition::Replace { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt LoopKind,
    ) -> <V as Monoid>::T {
        match v {
            LoopKind::UnconditionalLoop { .. } => V::identity(),
            LoopKind::WhileLoop { condition } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition);
                visitor_reduce_value
            }
            LoopKind::ForLoop { pat, iterator } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(iterator));
                visitor_reduce_value
            }
            LoopKind::ForIndexLoop {
                start,
                end,
                var,
                var_ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(start);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(end));
                V::append(&mut visitor_reduce_value, visitor.visit_ty(var_ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> <V as Monoid>::T {
        match v {
            ControlFlowKind::BreakOnly { .. } => V::identity(),
            ControlFlowKind::BreakOrReturn { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt LoopState,
    ) -> <V as Monoid>::T {
        match v {
            LoopState { init, body_pat } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(init);
                V::append(&mut visitor_reduce_value, visitor.visit_pat(body_pat));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ExprKind,
    ) -> <V as Monoid>::T {
        match v {
            ExprKind::If {
                condition,
                then,
                else_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(condition);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(then));
                visitor_reduce_value
            }
            ExprKind::App {
                head,
                args,
                generic_args,
                bounds_impls,
                trait_,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(head);
                for visitor_item in args {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                for visitor_item in generic_args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                for visitor_item in bounds_impls {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_expr(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ExprKind::Literal { .. } => V::identity(),
            ExprKind::Array(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_expr(visitor_item_1),
                        );
                    };
                }
                visitor_reduce_value
            }
            ExprKind::Match { scrutinee, arms } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(scrutinee);
                for visitor_item in arms {
                    V::append(&mut visitor_reduce_value, visitor.visit_arm(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Tuple(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in anon_field_0 {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Borrow { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner);
                visitor_reduce_value
            }
            ExprKind::AddressOf { mutable, inner } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(inner);
                visitor_reduce_value
            }
            ExprKind::Deref(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(anon_field_0);
                visitor_reduce_value
            }
            ExprKind::Let { lhs, rhs, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(rhs));
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                visitor_reduce_value
            }
            ExprKind::GlobalId { .. } => V::identity(),
            ExprKind::LocalId { .. } => V::identity(),
            ExprKind::Ascription { e, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(e);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            ExprKind::Assign { lhs, value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_lhs(lhs);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(value));
                visitor_reduce_value
            }
            ExprKind::Loop {
                body,
                kind,
                state,
                control_flow,
                label,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                V::append(&mut visitor_reduce_value, visitor.visit_loop_kind(kind));
                visitor_reduce_value
            }
            ExprKind::Break { value, label } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value);
                visitor_reduce_value
            }
            ExprKind::Return { value } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(value);
                visitor_reduce_value
            }
            ExprKind::Continue { .. } => V::identity(),
            ExprKind::Closure {
                params,
                body,
                captures,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_pat(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                for visitor_item in captures {
                    V::append(&mut visitor_reduce_value, visitor.visit_expr(visitor_item));
                }
                visitor_reduce_value
            }
            ExprKind::Block { body, safety_mode } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_expr(body);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_safety_kind(safety_mode),
                );
                visitor_reduce_value
            }
            ExprKind::Quote { contents } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(contents);
                visitor_reduce_value
            }
            ExprKind::Error { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericParamKind,
    ) -> <V as Monoid>::T {
        match v {
            GenericParamKind::Lifetime { .. } => V::identity(),
            GenericParamKind::Type { .. } => V::identity(),
            GenericParamKind::Const { ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_goal<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt TraitGoal,
    ) -> <V as Monoid>::T {
        match v {
            TraitGoal { trait_, args } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in args {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_value(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ImplIdent,
    ) -> <V as Monoid>::T {
        match v {
            ImplIdent { goal, name } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_trait_goal(goal);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ProjectionPredicate,
    ) -> <V as Monoid>::T {
        match v {
            ProjectionPredicate {
                impl_,
                assoc_item,
                ty,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_expr(impl_);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericConstraint,
    ) -> <V as Monoid>::T {
        match v {
            GenericConstraint::Lifetime { .. } => V::identity(),
            GenericConstraint::Type(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_impl_ident(anon_field_0);
                visitor_reduce_value
            }
            GenericConstraint::Projection(anon_field_0) => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_projection_predicate(anon_field_0);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt GenericParam,
    ) -> <V as Monoid>::T {
        match v {
            GenericParam { ident, meta, kind } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_metadata(meta);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_generic_param_kind(kind),
                );
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Generics,
    ) -> <V as Monoid>::T {
        match v {
            Generics {
                params,
                constraints,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in params {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_param(visitor_item),
                    );
                }
                for visitor_item in constraints {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_generic_constraint(visitor_item),
                    );
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_safety_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt SafetyKind,
    ) -> <V as Monoid>::T {
        match v {
            SafetyKind::Safe { .. } => V::identity(),
            SafetyKind::Unsafe { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Attribute,
    ) -> <V as Monoid>::T {
        match v {
            Attribute { kind, span } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_attribute_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt AttributeKind,
    ) -> <V as Monoid>::T {
        match v {
            AttributeKind::Tool { .. } => V::identity(),
            AttributeKind::DocComment { kind, body } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_doc_comment_kind(kind);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_doc_comment_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> <V as Monoid>::T {
        match v {
            DocCommentKind::Line { .. } => V::identity(),
            DocCommentKind::Block { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt SpannedTy,
    ) -> <V as Monoid>::T {
        match v {
            SpannedTy { span, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_ty(ty);
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Param,
    ) -> <V as Monoid>::T {
        match v {
            Param {
                pat,
                ty,
                ty_span,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_pat(pat);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_variant<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Variant,
    ) -> <V as Monoid>::T {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = V::identity();
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        V::append(&mut visitor_reduce_value, visitor.visit_ty(visitor_item_1));
                        ();
                    };
                }
                visitor_reduce_value
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt ItemKind,
    ) -> <V as Monoid>::T {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_expr(body));
                for visitor_item in params {
                    V::append(&mut visitor_reduce_value, visitor.visit_param(visitor_item));
                }
                V::append(&mut visitor_reduce_value, visitor.visit_safety_kind(safety));
                visitor_reduce_value
            }
            ItemKind::TyAlias { name, generics, ty } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(ty));
                visitor_reduce_value
            }
            ItemKind::Type {
                name,
                generics,
                variants,
                is_struct,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                for visitor_item in variants {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_variant(visitor_item),
                    );
                }
                visitor_reduce_value
            }
            ItemKind::Trait {
                name,
                generics,
                items,
            } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_trait_item(visitor_item),
                    );
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
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_generics(generics);
                V::append(&mut visitor_reduce_value, visitor.visit_ty(self_ty));
                {
                    let (visitor_item_0, visitor_item_1) = of_trait;
                    ();
                    for visitor_item in visitor_item_1 {
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_generic_value(visitor_item),
                        );
                    }
                };
                for visitor_item in items {
                    V::append(
                        &mut visitor_reduce_value,
                        visitor.visit_impl_item(visitor_item),
                    );
                }
                for visitor_item in parent_bounds {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_expr(visitor_item_0),
                        );
                        V::append(
                            &mut visitor_reduce_value,
                            visitor.visit_impl_ident(visitor_item_1),
                        );
                    };
                }
                V::append(&mut visitor_reduce_value, visitor.visit_safety_kind(safety));
                visitor_reduce_value
            }
            ItemKind::Alias { .. } => V::identity(),
            ItemKind::Use { .. } => V::identity(),
            ItemKind::Quote { quote, origin } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_quote(quote);
                V::append(
                    &mut visitor_reduce_value,
                    visitor.visit_item_quote_origin(origin),
                );
                visitor_reduce_value
            }
            ItemKind::Error { .. } => V::identity(),
            ItemKind::NotImplementedYet { .. } => V::identity(),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: VisitorReduce<'lt> + Monoid>(
        visitor: &mut V,
        v: &'lt Item,
    ) -> <V as Monoid>::T {
        match v {
            Item { ident, kind, meta } => {
                let mut visitor_reduce_value: <V as Monoid>::T;
                visitor_reduce_value = visitor.visit_item_kind(kind);
                V::append(&mut visitor_reduce_value, visitor.visit_metadata(meta));
                visitor_reduce_value
            }
        }
    }
}
mod visitor {
    use super::*;
    #[doc = "Fold visitor for the abstract syntax tree of hax. Visits nodes of each type of the AST."]
    pub trait Visitor<'lt>: Sized {
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
    pub fn visit_generic_value<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt GenericValue) -> () {
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
    pub fn visit_primitive_ty<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt PrimitiveTy) -> () {
        match v {
            PrimitiveTy::Bool { .. } => (),
            PrimitiveTy::Int { .. } => (),
            PrimitiveTy::Float { .. } => (),
            PrimitiveTy::Char { .. } => (),
            PrimitiveTy::Str { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_region<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Region) -> () {
        match v {
            Region { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_ty<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Ty) -> () {
        match v {
            Ty(anon_field_0) => {
                visitor.visit_ty_kind(anon_field_0.deref());
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_ty_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt TyKind) -> () {
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
            TyKind::Param { .. } => (),
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
                ()
            }
            TyKind::Opaque { .. } => (),
            TyKind::Dyn(anon_field_0) => {
                for visitor_item in anon_field_0 {
                    visitor.visit_dyn_trait_goal(visitor_item);
                }
                ()
            }
            TyKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_dyn_trait_goal<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt DynTraitGoal) -> () {
        match v {
            DynTraitGoal {
                trait_,
                non_self_args,
            } => {
                for visitor_item in non_self_args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_metadata<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Metadata) -> () {
        match v {
            Metadata { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_expr<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Expr) -> () {
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
    pub fn visit_pat<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Pat) -> () {
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
    pub fn visit_arm<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Arm) -> () {
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
    pub fn visit_guard<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Guard) -> () {
        match v {
            Guard { kind, meta } => {
                visitor.visit_guard_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_borrow_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt BorrowKind) -> () {
        match v {
            BorrowKind::Shared { .. } => (),
            BorrowKind::Unique { .. } => (),
            BorrowKind::Mut { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_binding_mode<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt BindingMode) -> () {
        match v {
            BindingMode::ByValue { .. } => (),
            BindingMode::ByRef(anon_field_0) => {
                visitor.visit_borrow_kind(anon_field_0);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_pat_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt PatKind) -> () {
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
            PatKind::Constant { .. } => (),
            PatKind::Binding {
                mutable,
                var,
                mode,
                sub_pat,
            } => {
                visitor.visit_binding_mode(mode);
                ()
            }
            PatKind::Construct {
                constructor,
                is_record,
                is_struct,
                fields,
            } => {
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
                        visitor.visit_pat(visitor_item_1);
                    };
                }
                ()
            }
            PatKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_guard_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt GuardKind) -> () {
        match v {
            GuardKind::IfLet { lhs, rhs } => {
                visitor.visit_pat(lhs);
                visitor.visit_expr(rhs);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_lhs<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Lhs) -> () {
        match v {
            Lhs::LocalVar { var, ty } => {
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
    pub fn visit_impl_expr<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ImplExpr) -> () {
        match v {
            ImplExpr { kind, goal } => {
                visitor.visit_impl_expr_kind(kind.deref());
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_expr_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ImplExprKind) -> () {
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
    pub fn visit_impl_item<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ImplItem) -> () {
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
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_item_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ImplItemKind) -> () {
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
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt TraitItem) -> () {
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
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_trait_item_kind<'lt, V: Visitor<'lt>>(
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
        }
    }
    #[allow(unused)]
    pub fn visit_quote_content<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt QuoteContent) -> () {
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
    pub fn visit_quote<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Quote) -> () {
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
    pub fn visit_item_quote_origin<'lt, V: Visitor<'lt>>(
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
                visitor.visit_item_quote_origin_position(position);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_quote_origin_kind<'lt, V: Visitor<'lt>>(
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
    pub fn visit_item_quote_origin_position<'lt, V: Visitor<'lt>>(
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
    pub fn visit_loop_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt LoopKind) -> () {
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
                visitor.visit_ty(var_ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_control_flow_kind<'lt, V: Visitor<'lt>>(
        visitor: &mut V,
        v: &'lt ControlFlowKind,
    ) -> () {
        match v {
            ControlFlowKind::BreakOnly { .. } => (),
            ControlFlowKind::BreakOrReturn { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_loop_state<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt LoopState) -> () {
        match v {
            LoopState { init, body_pat } => {
                visitor.visit_expr(init);
                visitor.visit_pat(body_pat);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_expr_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ExprKind) -> () {
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
            ExprKind::Literal { .. } => (),
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
                for visitor_item in fields {
                    {
                        let (visitor_item_0, visitor_item_1) = visitor_item;
                        ();
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
            ExprKind::GlobalId { .. } => (),
            ExprKind::LocalId { .. } => (),
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
            ExprKind::Error { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_generic_param_kind<'lt, V: Visitor<'lt>>(
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
    pub fn visit_trait_goal<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt TraitGoal) -> () {
        match v {
            TraitGoal { trait_, args } => {
                for visitor_item in args {
                    visitor.visit_generic_value(visitor_item);
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_impl_ident<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ImplIdent) -> () {
        match v {
            ImplIdent { goal, name } => {
                visitor.visit_trait_goal(goal);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_projection_predicate<'lt, V: Visitor<'lt>>(
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
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generic_constraint<'lt, V: Visitor<'lt>>(
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
    pub fn visit_generic_param<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt GenericParam) -> () {
        match v {
            GenericParam { ident, meta, kind } => {
                visitor.visit_metadata(meta);
                visitor.visit_generic_param_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_generics<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Generics) -> () {
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
    pub fn visit_safety_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt SafetyKind) -> () {
        match v {
            SafetyKind::Safe { .. } => (),
            SafetyKind::Unsafe { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_attribute<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Attribute) -> () {
        match v {
            Attribute { kind, span } => {
                visitor.visit_attribute_kind(kind);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_attribute_kind<'lt, V: Visitor<'lt>>(
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
    pub fn visit_doc_comment_kind<'lt, V: Visitor<'lt>>(
        visitor: &mut V,
        v: &'lt DocCommentKind,
    ) -> () {
        match v {
            DocCommentKind::Line { .. } => (),
            DocCommentKind::Block { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_spanned_ty<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt SpannedTy) -> () {
        match v {
            SpannedTy { span, ty } => {
                visitor.visit_ty(ty);
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_param<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Param) -> () {
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
    pub fn visit_variant<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Variant) -> () {
        match v {
            Variant {
                name,
                arguments,
                is_record,
                attributes,
            } => {
                for visitor_item in arguments {
                    {
                        let (visitor_item_0, visitor_item_1, visitor_item_2) = visitor_item;
                        ();
                        visitor.visit_ty(visitor_item_1);
                        ();
                    };
                }
                ()
            }
        }
    }
    #[allow(unused)]
    pub fn visit_item_kind<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt ItemKind) -> () {
        match v {
            ItemKind::Fn {
                name,
                generics,
                body,
                params,
                safety,
            } => {
                visitor.visit_generics(generics);
                visitor.visit_expr(body);
                for visitor_item in params {
                    visitor.visit_param(visitor_item);
                }
                visitor.visit_safety_kind(safety);
                ()
            }
            ItemKind::TyAlias { name, generics, ty } => {
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
                    ();
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
            ItemKind::Alias { .. } => (),
            ItemKind::Use { .. } => (),
            ItemKind::Quote { quote, origin } => {
                visitor.visit_quote(quote);
                visitor.visit_item_quote_origin(origin);
                ()
            }
            ItemKind::Error { .. } => (),
            ItemKind::NotImplementedYet { .. } => (),
        }
    }
    #[allow(unused)]
    pub fn visit_item<'lt, V: Visitor<'lt>>(visitor: &mut V, v: &'lt Item) -> () {
        match v {
            Item { ident, kind, meta } => {
                visitor.visit_item_kind(kind);
                visitor.visit_metadata(meta);
                ()
            }
        }
    }
}
