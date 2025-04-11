//! Reconstruct structured expressions from rustc's various constant representations.
use super::*;
use rustc_const_eval::interpret::{interp_ok, InterpResult};
use rustc_middle::mir::interpret;
use rustc_middle::{mir, ty};

impl ConstantLiteral {
    /// Rustc always represents string constants as `&[u8]`, but this
    /// is not nice to consume. This associated function interpret
    /// bytes as an unicode string, and as a byte string otherwise.
    fn byte_str(bytes: Vec<u8>) -> Self {
        match String::from_utf8(bytes.clone()) {
            Ok(s) => Self::Str(s),
            Err(_) => Self::ByteStr(bytes),
        }
    }
}

#[tracing::instrument(level = "trace", skip(s))]
pub(crate) fn scalar_int_to_constant_literal<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    x: rustc_middle::ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> ConstantLiteral {
    match ty.kind() {
        ty::Char => ConstantLiteral::Char(
            char::try_from(x).s_expect(s, "scalar_int_to_constant_literal: expected a char"),
        ),
        ty::Bool => ConstantLiteral::Bool(
            x.try_to_bool()
                .s_expect(s, "scalar_int_to_constant_literal: expected a bool"),
        ),
        ty::Int(kind) => {
            let v = x.to_int(x.size());
            ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
        }
        ty::Uint(kind) => {
            let v = x.to_uint(x.size());
            ConstantLiteral::Int(ConstantInt::Uint(v, kind.sinto(s)))
        }
        ty::Float(kind) => {
            let v = x.to_bits_unchecked();
            bits_and_type_to_float_constant_literal(v, kind.sinto(s))
        }
        _ => {
            let ty_sinto: Ty = ty.sinto(s);
            supposely_unreachable_fatal!(
                s,
                "scalar_int_to_constant_literal_ExpectedLiteralType";
                { ty, ty_sinto, x }
            )
        }
    }
}

/// Converts a bit-representation of a float of type `ty` to a constant literal
fn bits_and_type_to_float_constant_literal(bits: u128, ty: FloatTy) -> ConstantLiteral {
    use rustc_apfloat::{ieee, Float};
    let string = match &ty {
        FloatTy::F16 => ieee::Half::from_bits(bits).to_string(),
        FloatTy::F32 => ieee::Single::from_bits(bits).to_string(),
        FloatTy::F64 => ieee::Double::from_bits(bits).to_string(),
        FloatTy::F128 => ieee::Quad::from_bits(bits).to_string(),
    };
    ConstantLiteral::Float(string, ty)
}

impl ConstantExprKind {
    pub fn decorate(self, ty: Ty, span: Span) -> Decorated<Self> {
        Decorated {
            contents: Box::new(self),
            hir_id: None,
            attributes: vec![],
            ty,
            span,
        }
    }
}

/// Whether a `DefId` is a `AnonConst`. An anonymous constant is
/// generated by Rustc, hoisting every constat bits from items as
/// separate top-level items. This AnonConst mechanism is internal to
/// Rustc; we don't want to reflect that, instead we prefer inlining
/// those. `is_anon_const` is used to detect such AnonConst so that we
/// can evaluate and inline them.
pub(crate) fn is_anon_const(
    did: rustc_span::def_id::DefId,
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> bool {
    matches!(
        tcx.def_kind(did),
        rustc_hir::def::DefKind::AnonConst | rustc_hir::def::DefKind::InlineConst
    )
}

/// Attempts to translate a `ty::UnevaluatedConst` into a constant expression. This handles cases
/// of references to top-level or associated constants. Returns `None` if the input was not a named
/// constant.
pub fn translate_constant_reference<'tcx>(
    s: &impl UnderOwnerState<'tcx>,
    span: rustc_span::Span,
    ucv: rustc_middle::ty::UnevaluatedConst<'tcx>,
) -> Option<ConstantExpr> {
    let tcx = s.base().tcx;
    if is_anon_const(ucv.def, tcx) {
        return None;
    }
    let typing_env = s.typing_env();
    let ty = s.base().tcx.type_of(ucv.def).instantiate(tcx, ucv.args);
    let ty = tcx
        .try_normalize_erasing_regions(typing_env, ty)
        .unwrap_or(ty);
    let kind = if let Some(assoc) = s.base().tcx.opt_associated_item(ucv.def) {
        if assoc.trait_item_def_id.is_some() {
            // This must be a trait declaration constant
            let name = assoc.name.to_string();
            let impl_expr = self_clause_for_item(s, &assoc, ucv.args).unwrap();
            ConstantExprKind::TraitConst { impl_expr, name }
        } else {
            // Constant appearing in an inherent impl block.
            let parent_def_id = tcx.parent(ucv.def);
            let trait_refs = solve_item_required_traits(s, parent_def_id, ucv.args);
            ConstantExprKind::GlobalName {
                id: ucv.def.sinto(s),
                generics: ucv.args.sinto(s),
                trait_refs,
            }
        }
    } else {
        // Top-level constant.
        ConstantExprKind::GlobalName {
            id: ucv.def.sinto(s),
            generics: ucv.args.sinto(s),
            trait_refs: vec![],
        }
    };
    let cv = kind.decorate(ty.sinto(s), span.sinto(s));
    Some(cv)
}

/// Evaluate a `ty::Const`.
pub fn eval_ty_constant<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    c: ty::Const<'tcx>,
) -> Option<ty::Const<'tcx>> {
    let tcx = s.base().tcx;
    let evaluated = tcx.try_normalize_erasing_regions(s.typing_env(), c).ok()?;
    (evaluated != c).then_some(evaluated)
}

/// Evaluate a `mir::Const`.
pub fn eval_mir_constant<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    c: mir::Const<'tcx>,
) -> Option<mir::Const<'tcx>> {
    let evaluated = c
        .eval(s.base().tcx, s.typing_env(), rustc_span::DUMMY_SP)
        .ok()?;
    let evaluated = mir::Const::Val(evaluated, c.ty());
    (evaluated != c).then_some(evaluated)
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for ty::Const<'tcx> {
    #[tracing::instrument(level = "trace", skip(s))]
    fn sinto(&self, s: &S) -> ConstantExpr {
        use rustc_middle::query::Key;
        let span = self.default_span(s.base().tcx);
        match self.kind() {
            ty::ConstKind::Param(p) => {
                let ty = p.find_ty_from_env(s.param_env());
                let kind = ConstantExprKind::ConstRef { id: p.sinto(s) };
                kind.decorate(ty.sinto(s), span.sinto(s))
            }
            ty::ConstKind::Infer(..) => {
                fatal!(s[span], "ty::ConstKind::Infer node? {:#?}", self)
            }

            ty::ConstKind::Unevaluated(ucv) => match translate_constant_reference(s, span, ucv) {
                Some(val) => val,
                None => match eval_ty_constant(s, *self) {
                    Some(val) => val.sinto(s),
                    // TODO: This is triggered when compiling using `generic_const_exprs`
                    None => supposely_unreachable_fatal!(s, "TranslateUneval"; {self, ucv}),
                },
            },

            ty::ConstKind::Value(val) => valtree_to_constant_expr(s, val.valtree, val.ty, span),
            ty::ConstKind::Error(_) => fatal!(s[span], "ty::ConstKind::Error"),
            ty::ConstKind::Expr(e) => fatal!(s[span], "ty::ConstKind::Expr {:#?}", e),

            ty::ConstKind::Bound(i, bound) => {
                supposely_unreachable_fatal!(s[span], "ty::ConstKind::Bound"; {i, bound});
            }
            _ => fatal!(s[span], "unexpected case"),
        }
    }
}

#[tracing::instrument(level = "trace", skip(s))]
pub(crate) fn valtree_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    valtree: rustc_middle::ty::ValTree<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> ConstantExpr {
    let kind = match (&*valtree, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) => {
            ConstantExprKind::Borrow(valtree_to_constant_expr(s, valtree, *inner_ty, span))
        }
        (ty::ValTreeKind::Branch(valtrees), ty::Str) => {
            let bytes = valtrees
                .iter()
                .map(|x| match &***x {
                    ty::ValTreeKind::Leaf(leaf) => leaf.to_u8(),
                    _ => fatal!(
                        s[span],
                        "Expected a flat list of leaves while translating \
                            a str literal, got a arbitrary valtree."
                    ),
                })
                .collect();
            ConstantExprKind::Literal(ConstantLiteral::byte_str(bytes))
        }
        (ty::ValTreeKind::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .base()
                .tcx
                .destructure_const(ty::Const::new_value(s.base().tcx, valtree, ty));
            let fields = contents.fields.iter().copied();
            match ty.kind() {
                ty::Array(_, _) => ConstantExprKind::Array {
                    fields: fields.map(|field| field.sinto(s)).collect(),
                },
                ty::Tuple(_) => ConstantExprKind::Tuple {
                    fields: fields.map(|field| field.sinto(s)).collect(),
                },
                ty::Adt(def, _) => {
                    let variant_idx = contents
                        .variant
                        .s_expect(s, "destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);

                    ConstantExprKind::Adt {
                        info: get_variant_information(def, variant_idx, s),
                        fields: fields
                            .into_iter()
                            .zip(&variant_def.fields)
                            .map(|(value, field)| ConstantFieldExpr {
                                field: field.did.sinto(s),
                                value: value.sinto(s),
                            })
                            .collect(),
                    }
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTreeKind::Leaf(x), ty::RawPtr(_, _)) => {
            use crate::rustc_type_ir::inherent::Ty;
            let raw_address = x.to_bits_unchecked();
            let uint_ty = UintTy::Usize;
            let usize_ty = rustc_middle::ty::Ty::new_usize(s.base().tcx).sinto(s);
            let lit = ConstantLiteral::Int(ConstantInt::Uint(raw_address, uint_ty));
            ConstantExprKind::Cast {
                source: ConstantExprKind::Literal(lit).decorate(usize_ty, span.sinto(s)),
            }
        }
        (ty::ValTreeKind::Leaf(x), _) => {
            ConstantExprKind::Literal(scalar_int_to_constant_literal(s, *x, ty))
        }
        _ => supposely_unreachable_fatal!(
            s[span], "valtree_to_expr";
            {valtree, ty}
        ),
    };
    kind.decorate(ty.sinto(s), span.sinto(s))
}

/// Use the const-eval interpreter to convert an evaluated operand back to a structured
/// constant expression.
fn op_to_const<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    span: rustc_span::Span,
    ecx: &rustc_const_eval::const_eval::CompileTimeInterpCx<'tcx>,
    op: rustc_const_eval::interpret::OpTy<'tcx>,
) -> InterpResult<'tcx, ConstantExpr> {
    use crate::rustc_const_eval::interpret::Projectable;
    // Code inspired from `try_destructure_mir_constant_for_user_output` and
    // `const_eval::eval_queries::op_to_const`.
    let tcx = s.base().tcx;
    let ty = op.layout.ty;
    // Helper for struct-likes.
    let read_fields = |of: rustc_const_eval::interpret::OpTy<'tcx>, field_count| {
        (0..field_count).map(move |i| {
            let field_op = ecx.project_field(&of, i)?;
            op_to_const(s, span, &ecx, field_op)
        })
    };
    let kind = match ty.kind() {
        // Detect statics
        _ if let Some(place) = op.as_mplace_or_imm().left()
            && let ptr = place.ptr()
            && let (alloc_id, _, _) = ecx.ptr_get_alloc_id(ptr, 0)?
            && let interpret::GlobalAlloc::Static(did) = tcx.global_alloc(alloc_id) =>
        {
            ConstantExprKind::GlobalName {
                id: did.sinto(s),
                generics: Vec::new(),
                trait_refs: Vec::new(),
            }
        }
        ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_) => {
            let scalar = ecx.read_scalar(&op)?;
            let scalar_int = scalar.try_to_scalar_int().unwrap();
            let lit = scalar_int_to_constant_literal(s, scalar_int, ty);
            ConstantExprKind::Literal(lit)
        }
        ty::Adt(adt_def, ..) if !adt_def.is_union() => {
            let variant = ecx.read_discriminant(&op)?;
            let down = ecx.project_downcast(&op, variant)?;
            let field_count = adt_def.variants()[variant].fields.len();
            let fields = read_fields(down, field_count)
                .zip(&adt_def.variant(variant).fields)
                .map(|(value, field)| {
                    interp_ok(ConstantFieldExpr {
                        field: field.did.sinto(s),
                        value: value?,
                    })
                })
                .collect::<InterpResult<Vec<_>>>()?;
            let variants_info = get_variant_information(adt_def, variant, s);
            ConstantExprKind::Adt {
                info: variants_info,
                fields,
            }
        }
        ty::Tuple(args) => {
            let fields = read_fields(op, args.len()).collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Tuple { fields }
        }
        ty::Array(..) | ty::Slice(..) => {
            let len = op.len(ecx)?;
            let fields = (0..len)
                .map(|i| {
                    let op = ecx.project_index(&op, i)?;
                    op_to_const(s, span, ecx, op)
                })
                .collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Array { fields }
        }
        ty::Str => {
            let str = ecx.read_str(&op.assert_mem_place())?;
            ConstantExprKind::Literal(ConstantLiteral::Str(str.to_owned()))
        }
        ty::FnDef(def_id, args) => {
            let (def_id, generics, generics_impls, method_impl) =
                get_function_from_def_id_and_generics(s, *def_id, args);
            ConstantExprKind::FnPtr {
                def_id,
                generics,
                generics_impls,
                method_impl,
            }
        }
        ty::RawPtr(..) | ty::Ref(..) => {
            let op = ecx.deref_pointer(&op)?;
            let val = op_to_const(s, span, ecx, op.into())?;
            match ty.kind() {
                ty::Ref(..) => ConstantExprKind::Borrow(val),
                ty::RawPtr(.., mutability) => ConstantExprKind::RawBorrow {
                    arg: val,
                    mutability: mutability.sinto(s),
                },
                _ => unreachable!(),
            }
        }
        _ => {
            fatal!(s[span], "Cannot convert constant back to an expression"; {op})
        }
    };
    let val = kind.decorate(ty.sinto(s), span.sinto(s));
    interp_ok(val)
}

pub fn const_value_to_constant_expr<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    ty: rustc_middle::ty::Ty<'tcx>,
    val: mir::ConstValue<'tcx>,
    span: rustc_span::Span,
) -> InterpResult<'tcx, ConstantExpr> {
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    let (ecx, op) =
        rustc_const_eval::const_eval::mk_eval_cx_for_const_val(tcx.at(span), typing_env, val, ty)
            .unwrap();
    op_to_const(s, span, &ecx, op)
}
