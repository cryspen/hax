use crate::prelude::*;
use rustc_hir::def::DefKind as RDefKind;
use rustc_middle::{mir, ty};

pub fn inst_binder<'tcx, T>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
    x: ty::EarlyBinder<'tcx, T>,
) -> T
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>> + Clone,
{
    match args {
        None => x.instantiate_identity(),
        Some(args) => tcx.normalize_erasing_regions(typing_env, x.instantiate(tcx, args)),
    }
}

pub fn substitute<'tcx, T>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
    x: T,
) -> T
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    inst_binder(tcx, typing_env, args, ty::EarlyBinder::bind(x))
}

#[extension_traits::extension(pub trait SubstBinder)]
impl<'tcx, T: ty::TypeFoldable<ty::TyCtxt<'tcx>>> ty::Binder<'tcx, T> {
    fn subst(
        self,
        tcx: ty::TyCtxt<'tcx>,
        generics: &[ty::GenericArg<'tcx>],
    ) -> ty::Binder<'tcx, T> {
        ty::EarlyBinder::bind(self).instantiate(tcx, generics)
    }
}

/// Whether the item can have generic parameters.
pub(crate) fn can_have_generics<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> bool {
    use RDefKind::*;
    match get_def_kind(tcx, def_id) {
        Mod | ConstParam | TyParam | LifetimeParam | Macro(..) | ExternCrate | Use | ForeignMod
        | GlobalAsm => false,
        _ => true,
    }
}

#[tracing::instrument(skip(s))]
pub(crate) fn get_variant_information<'s, S: UnderOwnerState<'s>>(
    adt_def: &ty::AdtDef<'s>,
    variant_index: rustc_abi::VariantIdx,
    s: &S,
) -> VariantInformations {
    fn is_named<'s, I: std::iter::Iterator<Item = &'s ty::FieldDef> + Clone>(it: I) -> bool {
        it.clone()
            .any(|field| field.name.to_ident_string().parse::<u64>().is_err())
    }
    let variant_def = adt_def.variant(variant_index);
    let variant = variant_def.def_id;
    let constructs_type: DefId = adt_def.did().sinto(s);
    let kind = if adt_def.is_struct() {
        let named = is_named(adt_def.all_fields());
        VariantKind::Struct { named }
    } else if adt_def.is_union() {
        VariantKind::Union
    } else {
        let named = is_named(variant_def.fields.iter());
        let index = variant_index.into();
        VariantKind::Enum { index, named }
    };
    VariantInformations {
        typ: constructs_type.clone(),
        variant: variant.sinto(s),
        kind,
        type_namespace: match &constructs_type.parent {
            Some(parent) => parent.clone(),
            None => {
                let span = s.base().tcx.def_span(variant);
                fatal!(
                    s[span],
                    "Type {:#?} appears to have no parent",
                    constructs_type
                )
            }
        },
    }
}

#[tracing::instrument(skip(sess))]
pub fn translate_span(span: rustc_span::Span, sess: &rustc_session::Session) -> Span {
    let smap: &rustc_span::source_map::SourceMap = sess.psess.source_map();
    let filename = smap.span_to_filename(span);

    let lo = smap.lookup_char_pos(span.lo());
    let hi = smap.lookup_char_pos(span.hi());

    Span {
        lo: lo.into(),
        hi: hi.into(),
        filename: filename.sinto(&()),
        rust_span_data: Some(span.data()),
    }
}

pub trait HasParamEnv<'tcx> {
    fn param_env(&self) -> ty::ParamEnv<'tcx>;
    fn typing_env(&self) -> ty::TypingEnv<'tcx>;
}

impl<'tcx, S: UnderOwnerState<'tcx>> HasParamEnv<'tcx> for S {
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        let tcx = self.base().tcx;
        let def_id = self.owner_id();
        if can_have_generics(tcx, def_id) {
            tcx.param_env(def_id)
        } else {
            ty::ParamEnv::empty()
        }
    }
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        ty::TypingEnv {
            param_env: self.param_env(),
            typing_mode: ty::TypingMode::PostAnalysis,
        }
    }
}

#[tracing::instrument(skip(s))]
pub(crate) fn attribute_from_scope<'tcx, S: ExprState<'tcx>>(
    s: &S,
    scope: &rustc_middle::middle::region::Scope,
) -> (Option<rustc_hir::hir_id::HirId>, Vec<Attribute>) {
    let owner = s.owner_id();
    let tcx = s.base().tcx;
    let scope_tree = tcx.region_scope_tree(owner);
    let hir_id = scope.hir_id(scope_tree);
    let tcx = s.base().tcx;
    let attributes = hir_id
        .map(|hir_id| tcx.hir_attrs(hir_id).sinto(s))
        .unwrap_or_default();
    (hir_id, attributes)
}

/// Gets the closest ancestor of `id` that is the id of a type.
pub fn get_closest_parent_type(
    tcx: &ty::TyCtxt,
    id: rustc_span::def_id::DefId,
) -> rustc_span::def_id::DefId {
    match tcx.def_kind(id) {
        rustc_hir::def::DefKind::Union
        | rustc_hir::def::DefKind::Struct
        | rustc_hir::def::DefKind::Enum => id,
        _ => get_closest_parent_type(tcx, tcx.parent(id)),
    }
}

/// Gets the visibility (`pub` or not) of the definition. Returns `None` for defs that don't have a
/// meaningful visibility.
pub fn get_def_visibility<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> Option<bool> {
    use RDefKind::*;
    match def_kind {
        AssocConst
        | AssocFn
        | Const
        | Enum
        | Field
        | Fn
        | ForeignTy
        | Macro { .. }
        | Mod
        | Static { .. }
        | Struct
        | Trait
        | TraitAlias
        | TyAlias { .. }
        | Union
        | Use
        | Variant => Some(tcx.visibility(def_id).is_public()),
        // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
        AnonConst
        | AssocTy
        | Closure
        | ConstParam
        | Ctor { .. }
        | ExternCrate
        | ForeignMod
        | GlobalAsm
        | Impl { .. }
        | InlineConst
        | LifetimeParam
        | OpaqueTy
        | SyntheticCoroutineBody
        | TyParam => None,
    }
}

/// Gets the attributes of the definition.
pub fn get_def_attrs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> &'tcx [rustc_hir::Attribute] {
    use RDefKind::*;
    match def_kind {
        // These kinds cause `get_attrs_unchecked` to panic.
        ConstParam | LifetimeParam | TyParam | ForeignMod => &[],
        _ => tcx.get_attrs_unchecked(def_id),
    }
}

/// Gets the children of a module.
pub fn get_mod_children<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
) -> Vec<(Option<rustc_span::Ident>, RDefId)> {
    match def_id.as_local() {
        Some(ldid) => match tcx.hir_node_by_def_id(ldid) {
            rustc_hir::Node::Crate(m)
            | rustc_hir::Node::Item(&rustc_hir::Item {
                kind: rustc_hir::ItemKind::Mod(_, m),
                ..
            }) => m
                .item_ids
                .iter()
                .map(|&item_id| {
                    let opt_ident = tcx.hir_item(item_id).kind.ident();
                    let def_id = item_id.owner_id.to_def_id();
                    (opt_ident, def_id)
                })
                .collect(),
            node => panic!("DefKind::Module is an unexpected node: {node:?}"),
        },
        None => tcx
            .module_children(def_id)
            .iter()
            .map(|child| (Some(child.ident), child.res.def_id()))
            .collect(),
    }
}

/// Gets the children of an `extern` block. Empty if the block is not defined in the current crate.
pub fn get_foreign_mod_children<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Vec<RDefId> {
    match def_id.as_local() {
        Some(ldid) => tcx
            .hir_node_by_def_id(ldid)
            .expect_item()
            .expect_foreign_mod()
            .1
            .iter()
            .map(|foreign_item_ref| foreign_item_ref.owner_id.to_def_id())
            .collect(),
        None => vec![],
    }
}

/// The signature of a method impl may be a subtype of the one expected from the trait decl, as in
/// the example below. For correctness, we must be able to map from the method generics declared in
/// the trait to the actual method generics. Because this would require type inference, we instead
/// simply return the declared signature. This will cause issues if it is possible to use such a
/// more-specific implementation with its more-specific type, but we have a few other issues with
/// lifetime-generic function pointers anyway so this is unlikely to cause problems.
///
/// ```ignore
/// trait MyCompare<Other>: Sized {
///     fn compare(self, other: Other) -> bool;
/// }
/// impl<'a> MyCompare<&'a ()> for &'a () {
///     // This implementation is more general because it works for non-`'a` refs. Note that only
///     // late-bound vars may differ in this way.
///     // `<&'a () as MyCompare<&'a ()>>::compare` has type `fn<'b>(&'a (), &'b ()) -> bool`,
///     // but type `fn(&'a (), &'a ()) -> bool` was expected from the trait declaration.
///     fn compare<'b>(self, _other: &'b ()) -> bool {
///         true
///     }
/// }
/// ```
pub fn get_method_sig<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: RDefId,
    method_args: Option<ty::GenericArgsRef<'tcx>>,
) -> ty::PolyFnSig<'tcx> {
    let real_sig = inst_binder(tcx, typing_env, method_args, tcx.fn_sig(def_id));
    let item = tcx.associated_item(def_id);
    if !matches!(item.container, ty::AssocItemContainer::Impl) {
        return real_sig;
    }
    let Some(decl_method_id) = item.trait_item_def_id else {
        return real_sig;
    };
    let declared_sig = tcx.fn_sig(decl_method_id);

    // TODO(Nadrieril): Temporary hack: if the signatures have the same number of bound vars, we
    // keep the real signature. While the declared signature is more correct, it is also less
    // normalized and we can't normalize without erasing regions but regions are crucial in
    // function signatures. Hence we cheat here, until charon gains proper normalization
    // capabilities.
    if declared_sig.skip_binder().bound_vars().len() == real_sig.bound_vars().len() {
        return real_sig;
    }

    let impl_def_id = item.container_id(tcx);
    let method_args =
        method_args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, def_id));
    // The trait predicate that is implemented by the surrounding impl block.
    let implemented_trait_ref = tcx
        .impl_trait_ref(impl_def_id)
        .unwrap()
        .instantiate(tcx, method_args);
    // Construct arguments for the declared method generics in the context of the implemented
    // method generics.
    let decl_args = method_args.rebase_onto(tcx, impl_def_id, implemented_trait_ref.args);
    let sig = declared_sig.instantiate(tcx, decl_args);
    // Avoids accidentally using the same lifetime name twice in the same scope
    // (once in impl parameters, second in the method declaration late-bound vars).
    let sig = tcx.anonymize_bound_vars(sig);
    normalize(tcx, typing_env, sig)
}

pub fn closure_once_shim<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    closure_ty: ty::Ty<'tcx>,
) -> Option<mir::Body<'tcx>> {
    let ty::Closure(def_id, args) = closure_ty.kind() else {
        unreachable!()
    };
    let instance = match args.as_closure().kind() {
        ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
            ty::Instance::fn_once_adapter_instance(tcx, *def_id, args)
        }
        ty::ClosureKind::FnOnce => return None,
    };
    let mir = tcx.instance_mir(instance.def).clone();
    let mir = ty::EarlyBinder::bind(mir).instantiate(tcx, instance.args);
    Some(mir)
}

pub fn drop_glue_shim<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    instantiate: Option<ty::GenericArgsRef<'tcx>>,
) -> Option<mir::Body<'tcx>> {
    let drop_in_place =
        tcx.require_lang_item(rustc_hir::LangItem::DropInPlace, rustc_span::DUMMY_SP);
    let ty = tcx.type_of(def_id);
    let ty = match instantiate {
        None => {
            if !tcx.generics_of(def_id).is_empty() {
                // Hack: layout code panics if it can't fully normalize types, which can happen e.g. with a
                // trait associated type. For now we only translate the glue for monomorphic types.
                return None;
            }
            ty.instantiate_identity()
        }
        Some(args) => ty.instantiate(tcx, args),
    };
    let instance_kind = ty::InstanceKind::DropGlue(drop_in_place, Some(ty));
    let mir = tcx.instance_mir(instance_kind).clone();
    Some(mir)
}
