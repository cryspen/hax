use crate::prelude::*;
use rustc_middle::ty;

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
        self.base().tcx.param_env(self.owner_id())
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
