use crate::prelude::*;
use tracing::trace;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::MirPhase, state: S as s)]
pub enum MirPhase {
    Built,
    Analysis(AnalysisPhase),
    Runtime(RuntimePhase),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::SourceInfo, state: S as s)]
pub struct SourceInfo {
    pub span: Span,
    pub scope: SourceScope,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::LocalDecl<'tcx>, state: S as s)]
pub struct LocalDecl {
    pub mutability: Mutability,
    pub local_info: ClearCrossCrate<LocalInfo>,
    pub internal: bool,
    pub ty: Ty,
    pub user_ty: Option<UserTypeProjections>,
    pub source_info: SourceInfo,
    #[value(None)]
    pub name: Option<String>, // This information is contextual, thus the SInto instance initializes it to None, and then we fill it while `SInto`ing MirBody
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ClearCrossCrate<T> {
    Clear,
    Set(T),
}

impl<S, TT, T: SInto<S, TT>> SInto<S, ClearCrossCrate<TT>>
    for rustc_middle::mir::ClearCrossCrate<T>
{
    fn sinto(&self, s: &S) -> ClearCrossCrate<TT> {
        match self {
            rustc_middle::mir::ClearCrossCrate::Clear => ClearCrossCrate::Clear,
            rustc_middle::mir::ClearCrossCrate::Set(x) => ClearCrossCrate::Set(x.sinto(s)),
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::RuntimePhase, state: S as _s)]
pub enum RuntimePhase {
    Initial,
    PostCleanup,
    Optimized,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::AnalysisPhase, state: S as _s)]
pub enum AnalysisPhase {
    Initial,
    PostCleanup,
}

pub type BasicBlocks = IndexVec<BasicBlock, BasicBlockData>;

fn name_of_local(
    local: rustc_middle::mir::Local,
    var_debug_info: &Vec<rustc_middle::mir::VarDebugInfo>,
) -> Option<String> {
    var_debug_info
        .into_iter()
        .find(|info| {
            if let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value {
                place.projection.is_empty() && place.local == local
            } else {
                false
            }
        })
        .map(|dbg| dbg.name.to_ident_string())
}

/// Enumerates the kinds of Mir bodies. TODO: use const generics
/// instead of an open list of types.
pub mod mir_kinds {
    use crate::prelude::{Deserialize, JsonSchema, Serialize};
    use rustc_data_structures::steal::Steal;
    use rustc_middle::mir::Body;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::def_id::LocalDefId;
    pub trait IsMirKind: Clone {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>>;
    }
    #[derive(Clone, Copy, Debug, JsonSchema, Serialize, Deserialize)]
    pub struct Const;
    impl IsMirKind for Const {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
            tcx.mir_const(id)
        }
    }
    #[derive(Clone, Copy, Debug, JsonSchema, Serialize, Deserialize)]
    pub struct Built;
    impl IsMirKind for Built {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
            tcx.mir_built(id)
        }
    }
    // TODO: Add [Promoted] MIR
}
pub use mir_kinds::IsMirKind;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::Constant<'tcx>, state: S as s)]
pub struct Constant {
    pub span: Span,
    pub user_ty: Option<UserTypeAnnotationIndex>,
    pub literal: TypedConstantKind,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Body<'tcx>, state: S as s)]
pub struct MirBody<KIND> {
    #[map(x.clone().as_mut().sinto(s))]
    pub basic_blocks: BasicBlocks,
    pub phase: MirPhase,
    pub pass_count: usize,
    pub source: MirSource,
    pub source_scopes: IndexVec<SourceScope, SourceScopeData>,
    pub generator: Option<GeneratorInfo>,
    #[map({
        let mut local_decls: rustc_index::IndexVec<rustc_middle::mir::Local, LocalDecl> = x.iter().map(|local_decl| {
            local_decl.sinto(s)
        }).collect();
        local_decls.iter_enumerated_mut().for_each(|(local, local_decl)| {
            local_decl.name = name_of_local(local, &self.var_debug_info);
        });
        let local_decls: rustc_index::IndexVec<Local, LocalDecl> = local_decls.into_iter().collect();
        local_decls.into()
    })]
    pub local_decls: IndexVec<Local, LocalDecl>,
    pub user_type_annotations: CanonicalUserTypeAnnotations,
    pub arg_count: usize,
    pub spread_arg: Option<Local>,
    pub var_debug_info: Vec<VarDebugInfo>,
    pub span: Span,
    pub required_consts: Vec<Constant>,
    pub is_polymorphic: bool,
    pub injection_phase: Option<MirPhase>,
    pub tainted_by_errors: Option<ErrorGuaranteed>,
    #[value(std::marker::PhantomData)]
    pub _kind: std::marker::PhantomData<KIND>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::SourceScopeData<'tcx>, state: S as s)]
pub struct SourceScopeData {
    pub span: Span,
    pub parent_scope: Option<SourceScope>,
    pub inlined: Option<(Instance, Span)>,
    pub inlined_parent_scope: Option<SourceScope>,
    pub local_data: ClearCrossCrate<SourceScopeLocalData>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::Instance<'tcx>, state: S as s)]
pub struct Instance {
    pub def: InstanceDef,
    pub substs: Vec<GenericArg>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::SourceScopeLocalData, state: S as s)]
pub struct SourceScopeLocalData {
    pub lint_root: HirId,
    pub safety: Safety,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::mir::Safety, state: S as s)]
pub enum Safety {
    Safe,
    BuiltinUnsafe,
    FnUnsafe,
    ExplicitUnsafe(HirId),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Operand<'tcx>, state: S as s)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

impl Operand {
    pub(crate) fn ty(&self) -> &Ty {
        match self {
            Operand::Copy(p) | Operand::Move(p) => &p.ty,
            Operand::Constant(c) => &c.literal.typ,
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Terminator<'tcx>, state: S as s)]
pub struct Terminator {
    pub source_info: SourceInfo,
    pub kind: TerminatorKind,
}

pub(crate) fn get_function_from_def_id_and_substs<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> (DefId, Vec<GenericArg>, Vec<ImplExpr>, Option<TraitInfo>) {
    let tcx = s.base().tcx;
    let param_env = tcx.param_env(s.owner_id());

    // Retrieve the trait requirements for the **method**.
    // For instance, if we write:
    // ```
    // fn foo<T : Bar>(...)
    //            ^^^
    // ```
    let trait_refs = solve_item_traits(s, param_env, def_id, substs, None);

    // Check if this is a trait method call: retrieve the trait source if
    // it is the case (i.e., where does the method come from? Does it refer
    // to a top-level implementation? Or the method of a parameter? etc.).
    // At the same time, retrieve the trait obligations for this **trait**.
    // Remark: the trait obligations for the method are not the same as
    // the trait obligations for the trait. More precisely:
    //
    // ```
    // trait Foo<T : Bar> {
    //              ^^^^^
    //      trait level trait obligation
    //   fn baz(...) where T : ... {
    //      ...                ^^^
    //             method level trait obligation
    //   }
    // }
    // ```
    //
    // Also, a function doesn't need to belong to a trait to have trait
    // obligations:
    // ```
    // fn foo<T : Bar>(...)
    //            ^^^
    //     method level trait obligation
    // ```
    let (substs, source) = if let Some(assoc) = tcx.opt_associated_item(def_id) &&
        assoc.container == rustc_middle::ty::AssocItemContainer::TraitContainer {
        // There is an associated item, and it is a trait
        use tracing::*;
        trace!("def_id: {:?}", def_id);
        trace!("assoc: def_id: {:?}", assoc.def_id);

        // Retrieve the trait information
        let (trait_def_id, trait_info) = get_trait_info(s, def_id, substs, &assoc);

        // Compute the list of generic arguments applied to the *method* itself.
        //
        // For instance, if we have:
        // ```
        // trait Foo<T> {
        //   fn baz<U>(...) { ... }
        // }
        //
        // fn test<T : Foo<u32>(x: T) {
        //   x.baz(...);
        //   ...
        // }
        // ```
        // The substs will be the concatenation: `<T, u32, U>`
        // We count how many generic parameters the trait declaration has,
        // and truncate the substitution to get the parameters which apply
        // to the method (here, `<U>`)
        let params_info = get_params_info(s, trait_def_id);
        let num_trait_generics = params_info.num_generic_params;
        let all_generics: Vec<GenericArg> = substs.sinto(s);
        let truncated_substs = all_generics[num_trait_generics..].into();

        // Return
        (truncated_substs, Option::Some(trait_info))
    } else {
        // Regular function call
        (substs.sinto(s), Option::None)
    };

    (def_id.sinto(s), substs, trait_refs, source)
}

/// Return the [DefId] of the function referenced by an operand, with the
/// parameters substitution.
/// The [Operand] comes from a [TerminatorKind::Call].
/// Only supports calls to top-level functions (which are considered as constants
/// by rustc); doesn't support closures for now.
fn get_function_from_operand<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>(
    s: &S,
    func: &rustc_middle::mir::Operand<'tcx>,
) -> (
    FunOperand,
    Vec<GenericArg>,
    Vec<ImplExpr>,
    Option<TraitInfo>,
) {
    use std::ops::Deref;
    // Match on the func operand: it should be a constant as we don't support
    // closures for now.
    use rustc_middle::mir::{ConstantKind, Operand};
    use rustc_middle::ty::TyKind;
    match func {
        Operand::Constant(c) => {
            // Regular function case
            let c = c.deref();
            let (def_id, substs) = match &c.literal {
                ConstantKind::Ty(c) => {
                    // The type of the constant should be a FnDef, allowing
                    // us to retrieve the function's identifier and instantiation.
                    let c_ty = c.ty();
                    assert!(c_ty.is_fn());
                    match c_ty.kind() {
                        TyKind::FnDef(def_id, substs) => (*def_id, *substs),
                        _ => {
                            unreachable!();
                        }
                    }
                }
                ConstantKind::Val(_, c_ty) => {
                    // Same as for the `Ty` case above
                    assert!(c_ty.is_fn());
                    match c_ty.kind() {
                        TyKind::FnDef(def_id, substs) => (*def_id, *substs),
                        _ => {
                            unreachable!();
                        }
                    }
                }
                ConstantKind::Unevaluated(_, _) => {
                    unimplemented!();
                }
            };

            let (fun_id, substs, trait_refs, trait_info) =
                get_function_from_def_id_and_substs(s, def_id, substs);
            (FunOperand::Id(fun_id), substs, trait_refs, trait_info)
        }
        Operand::Move(place) => {
            // Closure case.
            // The closure can not have bound variables nor trait references,
            // so we don't need to extract generics, trait refs, etc.
            let body = s.mir();
            let ty = func.ty(&body.local_decls, s.base().tcx);
            trace!("type: {:?}", ty);
            trace!("type kind: {:?}", ty.kind());
            let sig = match ty.kind() {
                rustc_middle::ty::TyKind::FnPtr(sig) => sig,
                _ => unreachable!(),
            };
            trace!("FnPtr: {:?}", sig);
            let place = place.sinto(s);

            (FunOperand::Move(place), Vec::new(), Vec::new(), None)
        }
        Operand::Copy(_place) => {
            unimplemented!("{:?}", func);
        }
    }
}

fn translate_terminator_kind_call<'tcx, S: BaseState<'tcx> + HasMir<'tcx> + HasOwnerId>(
    s: &S,
    terminator: &rustc_middle::mir::TerminatorKind<'tcx>,
) -> TerminatorKind {
    if let rustc_middle::mir::TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        from_hir_call,
        fn_span,
    } = terminator
    {
        let (fun, substs, trait_refs, trait_info) = get_function_from_operand(s, func);

        TerminatorKind::Call {
            fun,
            substs,
            args: args.sinto(s),
            destination: destination.sinto(s),
            target: target.sinto(s),
            unwind: unwind.sinto(s),
            from_hir_call: from_hir_call.sinto(s),
            fn_span: fn_span.sinto(s),
            trait_refs,
            trait_info,
        }
    } else {
        unreachable!()
    }
}

// We don't use the LitIntType on purpose (we don't want the "unsuffixed" case)
#[derive(
    Clone, Copy, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum IntUintTy {
    Int(IntTy),
    Uint(UintTy),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ScalarInt {
    /// Little-endian representation of the integer
    pub data_le_bytes: [u8; 16],
    pub int_ty: IntUintTy,
}

// TODO: naming conventions: is "translate" ok?
/// Translate switch targets
fn translate_switch_targets<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    switch_ty: &Ty,
    targets: &rustc_middle::mir::SwitchTargets,
) -> SwitchTargets {
    let targets_vec: Vec<(u128, BasicBlock)> =
        targets.iter().map(|(v, b)| (v, b.sinto(s))).collect();

    match switch_ty {
        Ty::Bool => {
            // This is an: `if ... then ... else ...`
            assert!(targets_vec.len() == 1);
            // It seems the block targets are inverted
            let (test_val, otherwise_block) = targets_vec[0];

            assert!(test_val == 0);

            // It seems the block targets are inverted
            let if_block = targets.otherwise().sinto(s);

            SwitchTargets::If(if_block, otherwise_block)
        }
        Ty::Int(_) | Ty::Uint(_) => {
            let int_ty = match switch_ty {
                Ty::Int(ty) => IntUintTy::Int(*ty),
                Ty::Uint(ty) => IntUintTy::Uint(*ty),
                _ => unreachable!(),
            };

            // This is a: switch(int).
            // Convert all the test values to the proper values.
            let mut targets_map: Vec<(ScalarInt, BasicBlock)> = Vec::new();
            for (v, tgt) in targets_vec {
                // We need to reinterpret the bytes (`v as i128` is not correct)
                let v = ScalarInt {
                    data_le_bytes: v.to_le_bytes(),
                    int_ty,
                };
                targets_map.push((v, tgt));
            }
            let otherwise_block = targets.otherwise().sinto(s);

            SwitchTargets::SwitchInt(int_ty, targets_map, otherwise_block)
        }
        _ => {
            fatal!(s, "Unexpected switch_ty: {:?}", switch_ty)
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(BasicBlock, BasicBlock),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    SwitchInt(IntUintTy, Vec<(ScalarInt, BasicBlock)>, BasicBlock),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum FunOperand {
    /// Call to a top-level function designated by its id
    Id(DefId),
    /// Use of a closure
    Move(Place),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::TerminatorKind<'tcx>, state: S as s)]
pub enum TerminatorKind {
    Goto {
        target: BasicBlock,
    },
    #[custom_arm(
        rustc_middle::mir::TerminatorKind::SwitchInt { discr, targets } => {
          let discr = discr.sinto(s);
          let targets = translate_switch_targets(s, discr.ty(), targets);
          TerminatorKind::SwitchInt {
              discr,
              targets,
          }
        }
    )]
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    Resume,
    Terminate,
    Return,
    Unreachable,
    Drop {
        place: Place,
        target: BasicBlock,
        unwind: UnwindAction,
        replace: bool,
    },
    #[custom_arm(
        x @ rustc_middle::mir::TerminatorKind::Call { .. } => {
          translate_terminator_kind_call(s, x)
        }
    )]
    Call {
        fun: FunOperand,
        /// We truncate the substitution so as to only include the arguments
        /// relevant to the method (and not the trait) if it is a trait method
        /// call. See [ParamsInfo] for the full details.
        substs: Vec<GenericArg>,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
        unwind: UnwindAction,
        from_hir_call: bool,
        fn_span: Span,
        trait_refs: Vec<ImplExpr>,
        trait_info: Option<TraitInfo>,
    },
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BasicBlock,
        unwind: UnwindAction,
    },
    Yield {
        value: Operand,
        resume: BasicBlock,
        resume_arg: Place,
        drop: Option<BasicBlock>,
    },
    GeneratorDrop,
    FalseEdge {
        real_target: BasicBlock,
        imaginary_target: BasicBlock,
    },
    FalseUnwind {
        real_target: BasicBlock,
        unwind: UnwindAction,
    },
    InlineAsm {
        template: Vec<InlineAsmTemplatePiece>,
        operands: Vec<InlineAsmOperand>,
        options: InlineAsmOptions,
        line_spans: Vec<Span>,
        destination: Option<BasicBlock>,
        unwind: UnwindAction,
    },
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Statement<'tcx>, state: S as s)]
pub struct Statement {
    pub source_info: SourceInfo,
    #[map(Box::new(x.sinto(s)))]
    pub kind: Box<StatementKind>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::StatementKind<'tcx>, state: S as s)]
pub enum StatementKind {
    Assign((Place, Rvalue)),
    FakeRead((FakeReadCause, Place)),
    SetDiscriminant {
        place: Place,
        variant_index: VariantIdx,
    },
    Deinit(Place),
    StorageLive(Local),
    StorageDead(Local),
    Retag(RetagKind, Place),
    PlaceMention(Place),
    AscribeUserType((Place, UserTypeProjection), Variance),
    Coverage(Coverage),
    Intrinsic(NonDivergingIntrinsic),
    ConstEvalCounter,
    Nop,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Place {
    /// The type of the element on which we apply the projection given by `kind`
    pub ty: Ty,
    pub kind: PlaceKind,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PlaceKind {
    Local(Local),
    Projection {
        place: Box<Place>,
        kind: ProjectionElem,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ProjectionElemFieldKind {
    Tuple(FieldIdx),
    Adt {
        typ: DefId,
        variant: Option<VariantIdx>,
        index: FieldIdx,
    },
    /// Get access to one of the fields of the state of a closure
    ClosureState(FieldIdx),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ProjectionElem {
    Deref,
    Field(ProjectionElemFieldKind),
    Index(Local),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast(Option<Symbol>, VariantIdx),
    OpaqueCast,
}

// refactor
impl<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>> SInto<S, Place>
    for rustc_middle::mir::Place<'tcx>
{
    #[tracing::instrument(level = "info", skip(s))]
    fn sinto(&self, s: &S) -> Place {
        let local_decl = &s.mir().local_decls[self.local];
        let mut current_ty: rustc_middle::ty::Ty = local_decl.ty;
        let mut current_kind = PlaceKind::Local(self.local.sinto(s));
        let mut elems: &[rustc_middle::mir::PlaceElem] = self.projection.as_slice();

        loop {
            use rustc_middle::mir::ProjectionElem::*;
            let cur_ty = current_ty.clone();
            let cur_kind = current_kind.clone();
            use rustc_middle::ty::TyKind;
            let mk_field = |index: &rustc_abi::FieldIdx,
                            variant_idx: Option<rustc_abi::VariantIdx>| {
                ProjectionElem::Field(match cur_ty.kind() {
                    TyKind::Adt(adt_def, _) => {
                        assert!(
                            (adt_def.is_struct() && variant_idx.is_none())
                                || (adt_def.is_enum() && variant_idx.is_some())
                        );
                        ProjectionElemFieldKind::Adt {
                            typ: adt_def.did().sinto(s),
                            variant: variant_idx.map(|id| id.sinto(s)),
                            index: index.sinto(s),
                        }
                    }
                    TyKind::Tuple(_types) => ProjectionElemFieldKind::Tuple(index.sinto(s)),
                    ty_kind => {
                        supposely_unreachable_fatal!(
                            s, "ProjectionElemFieldBadType";
                            {index, ty_kind, variant_idx, &cur_ty, &cur_kind}
                        );
                    }
                })
            };
            let elem_kind: ProjectionElem = match elems {
                [Downcast(_, variant_idx), Field(index, ty), rest @ ..] => {
                    elems = rest;
                    let r = mk_field(index, Some(*variant_idx));
                    current_ty = ty.clone();
                    r
                }
                [elem, rest @ ..] => {
                    elems = rest;
                    use rustc_middle::ty::TyKind;
                    match elem {
                        Deref => {
                            current_ty = match current_ty.kind() {
                                TyKind::Ref(_, ty, _) => ty.clone(),
                                TyKind::Adt(def, substs) if def.is_box() => substs.type_at(0),
                                _ => supposely_unreachable_fatal!(
                                    s, "PlaceDerefNotRefNorBox";
                                    {current_ty, current_kind, elem}
                                ),
                            };
                            ProjectionElem::Deref
                        }
                        Field(index, ty) => {
                            if let TyKind::Closure(_, substs) = cur_ty.kind() {
                                // We get there when we access one of the fields
                                // of the the state captured by a closure.
                                use crate::rustc_index::Idx;
                                let substs = substs.as_closure();
                                let upvar_tys: Vec<_> = substs.upvar_tys().collect();
                                current_ty = upvar_tys[index.sinto(s).index()].clone();
                                ProjectionElem::Field(ProjectionElemFieldKind::ClosureState(
                                    index.sinto(s),
                                ))
                            } else {
                                let r = mk_field(index, None);
                                current_ty = ty.clone();
                                r
                            }
                        }
                        Index(local) => {
                            let (TyKind::Slice(ty) | TyKind::Array(ty, _)) = current_ty.kind()
                            else {
                                supposely_unreachable_fatal!(
                                    s,
                                    "PlaceIndexNotSlice";
                                    {current_ty, current_kind, elem}
                                );
                            };
                            current_ty = ty.clone();
                            ProjectionElem::Index(local.sinto(s))
                        }
                        ConstantIndex {
                            offset,
                            min_length,
                            from_end,
                        } => {
                            let TyKind::Slice(ty) = current_ty.kind() else {
                                supposely_unreachable_fatal!(
                                    s, "PlaceConstantIndexNotSlice";
                                    {current_ty, current_kind, elem}
                                )
                            };
                            current_ty = ty.clone();
                            ProjectionElem::ConstantIndex {
                                offset: *offset,
                                min_length: *min_length,
                                from_end: *from_end,
                            }
                        }
                        Subslice { from, to, from_end } =>
                        // TODO: We assume subslice preserves the type
                        {
                            ProjectionElem::Subslice {
                                from: *from,
                                to: *to,
                                from_end: *from_end,
                            }
                        }
                        OpaqueCast(ty) => {
                            current_ty = ty.clone();
                            ProjectionElem::OpaqueCast
                        }
                        Downcast { .. } => panic!("unexpected Downcast"),
                    }
                }
                [] => break,
            };

            current_kind = PlaceKind::Projection {
                place: Box::new(Place {
                    ty: cur_ty.sinto(s),
                    kind: current_kind.clone(),
                }),
                kind: elem_kind,
            };
        }
        Place {
            ty: current_ty.sinto(s),
            kind: current_kind.clone(),
        }
    }
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct MirFnSig {
    pub inputs: Vec<Ty>,
    pub output: Ty,
    pub c_variadic: bool,
    pub unsafety: Unsafety,
    pub abi: Abi,
}

pub type MirPolyFnSig = Binder<MirFnSig>;

impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, MirFnSig> for rustc_middle::ty::FnSig<'tcx> {
    fn sinto(&self, s: &S) -> MirFnSig {
        let inputs = self.inputs().sinto(s);
        let output = self.output().sinto(s);
        MirFnSig {
            inputs,
            output,
            c_variadic: self.c_variadic,
            unsafety: self.unsafety.sinto(s),
            abi: self.abi.sinto(s),
        }
    }
}

// TODO: we need this function because sometimes, Rust doesn't infer the proper
// typeclass instance.
pub(crate) fn poly_fn_sig_to_mir_poly_fn_sig<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    sig: &rustc_middle::ty::PolyFnSig<'tcx>,
    s: &S,
) -> MirPolyFnSig {
    sig.sinto(s)
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::AggregateKind<'tcx>, state: S as s)]
pub enum AggregateKind {
    Array(Ty),
    Tuple,
    #[custom_arm(rustc_middle::mir::AggregateKind::Adt(def_id, vid, substs, annot, fid) => {
        let adt_kind = s.base().tcx.adt_def(def_id).adt_kind().sinto(s);
        let param_env = s.base().tcx.param_env(s.owner_id());
        let trait_refs = solve_item_traits(s, param_env, *def_id, substs, None);
        AggregateKind::Adt(
            def_id.sinto(s),
            vid.sinto(s),
            adt_kind,
            substs.sinto(s),
            trait_refs,
            annot.sinto(s),
            fid.sinto(s))
    })]
    Adt(
        DefId,
        VariantIdx,
        AdtKind,
        Vec<GenericArg>,
        Vec<ImplExpr>,
        Option<UserTypeAnnotationIndex>,
        Option<FieldIdx>,
    ),
    #[custom_arm(rustc_middle::mir::AggregateKind::Closure(rust_id, substs) => {
        let def_id : DefId = rust_id.sinto(s);
        // The substs is meant to be converted to a function signature. Note
        // that Rustc does its job: the PolyFnSig binds the captured local
        // type, regions, etc. variables, which means we can treat the local
        // closure like any top-level function.
        let closure = substs.as_closure();
        let sig = closure.sig();
        let sig = poly_fn_sig_to_mir_poly_fn_sig(&sig, s);

        // Solve the trait obligations. Note that we solve the parent
        let tcx = s.base().tcx;
        let param_env = tcx.param_env(s.owner_id());
        let parent_substs = closure.parent_substs();
        let substs = tcx.mk_substs(parent_substs);
        // Retrieve the predicates from the parent (i.e., the function which calls
        // the closure).
        let predicates = tcx.predicates_defined_on(tcx.generics_of(rust_id).parent.unwrap());

        let trait_refs = solve_item_traits(s, param_env, *rust_id, substs, Some(predicates));
        AggregateKind::Closure(def_id, parent_substs.sinto(s), trait_refs, sig)
    })]
    Closure(DefId, Vec<GenericArg>, Vec<ImplExpr>, MirPolyFnSig),
    Generator(DefId, Vec<GenericArg>, Movability),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::CastKind, state: S as s)]
pub enum CastKind {
    PointerExposeAddress,
    PointerFromExposedAddress,
    Pointer(PointerCast),
    DynStar,
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::NullOp<'tcx>, state: S as s)]
pub enum NullOp {
    SizeOf,
    AlignOf,
    OffsetOf(Vec<FieldIdx>),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Rvalue<'tcx>, state: S as s)]
pub enum Rvalue {
    Use(Operand),
    #[custom_arm(
        rustc_middle::mir::Rvalue::Repeat(op, ce) => {
            let op = op.sinto(s);
            Rvalue::Repeat(op, ce.sinto(s))
        },
    )]
    Repeat(Operand, ConstantExpr),
    Ref(Region, BorrowKind, Place),
    ThreadLocalRef(DefId),
    AddressOf(Mutability, Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, (Operand, Operand)),
    CheckedBinaryOp(BinOp, (Operand, Operand)),
    NullaryOp(NullOp, Ty),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, IndexVec<FieldIdx, Operand>),
    ShallowInitBox(Operand, Ty),
    CopyForDeref(Place),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::BasicBlockData<'tcx>, state: S as s)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
    pub is_cleanup: bool,
}

pub type CanonicalUserTypeAnnotations =
    IndexVec<UserTypeAnnotationIndex, CanonicalUserTypeAnnotation>;

make_idx_wrapper!(rustc_middle::mir, BasicBlock);
make_idx_wrapper!(rustc_middle::mir, SourceScope);
make_idx_wrapper!(rustc_middle::mir, Local);
make_idx_wrapper!(rustc_middle::ty, UserTypeAnnotationIndex);
make_idx_wrapper!(rustc_abi, FieldIdx);

sinto_todo!(rustc_middle::ty, InstanceDef<'tcx>);
sinto_todo!(rustc_middle::mir, UserTypeProjections);
sinto_todo!(rustc_middle::mir, LocalInfo<'tcx>);
sinto_todo!(rustc_ast::ast, InlineAsmTemplatePiece);
sinto_todo!(rustc_ast::ast, InlineAsmOptions);
sinto_todo!(rustc_middle::mir, InlineAsmOperand<'tcx>);
sinto_todo!(rustc_middle::mir, AssertMessage<'tcx>);
sinto_todo!(rustc_middle::mir, UnwindAction);
sinto_todo!(rustc_middle::mir, FakeReadCause);
sinto_todo!(rustc_middle::mir, RetagKind);
sinto_todo!(rustc_middle::mir, Coverage);
sinto_todo!(rustc_middle::mir, NonDivergingIntrinsic<'tcx>);
sinto_todo!(rustc_middle::mir, UserTypeProjection);
sinto_todo!(rustc_middle::mir, MirSource<'tcx>);
sinto_todo!(rustc_middle::mir, GeneratorInfo<'tcx>);
sinto_todo!(rustc_middle::mir, VarDebugInfo<'tcx>);
sinto_todo!(rustc_span, ErrorGuaranteed);
