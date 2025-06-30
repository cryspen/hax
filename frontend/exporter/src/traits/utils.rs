//! Each item can involve three kinds of predicates:
//! - input aka required predicates: the predicates required to mention the item. These are usually `where`
//!   clauses (or equivalent) on the item:
//! ```ignore
//! struct Foo<T: Clone> { ... }
//! trait Foo<T> where T: Clone { ... }
//! fn function<I>() where I: Iterator, I::Item: Clone { ... }
//! ```
//! - output aka implied predicates: the predicates that are implied by the presence of this item in a
//!   signature. This is mostly trait parent predicates:
//! ```ignore
//! trait Foo: Clone { ... }
//! fn bar<T: Foo>() {
//!   // from `T: Foo` we can deduce `T: Clone`
//! }
//! ```
//!   This could also include implied predicates such as `&'a T` implying `T: 'a` but we don't
//!   consider these.
//! - "self" predicate: that's the special `Self: Trait` predicate in scope within a trait
//!   declaration or implementation for trait `Trait`.
//!
//! Note that within a given item the polarity is reversed: input predicates are the ones that can
//! be assumed to hold and output predicates must be proven to hold. The "self" predicate is both
//! assumed and proven within an impl block, and just assumed within a trait declaration block.
//!
//! The current implementation considers all predicates on traits to be outputs, which has the
//! benefit of reducing the size of signatures. Moreover, the rules on which bounds are required vs
//! implied are subtle. We may change this if this proves to be a problem.
use rustc_hir::def::DefKind;
use rustc_middle::ty::*;
use rustc_span::def_id::DefId;
use rustc_span::DUMMY_SP;

/// Returns a list of type predicates for the definition with ID `def_id`, including inferred
/// lifetime constraints. This is the basic list of predicates we use for essentially all items.
pub fn predicates_defined_on(tcx: TyCtxt<'_>, def_id: DefId) -> GenericPredicates<'_> {
    let mut result = tcx.explicit_predicates_of(def_id);
    let inferred_outlives = tcx.inferred_outlives_of(def_id);
    if !inferred_outlives.is_empty() {
        let inferred_outlives_iter = inferred_outlives
            .iter()
            .map(|(clause, span)| ((*clause).upcast(tcx), *span));
        result.predicates = tcx.arena.alloc_from_iter(
            result
                .predicates
                .into_iter()
                .copied()
                .chain(inferred_outlives_iter),
        );
    }
    result
}

/// The predicates that must hold to mention this item. E.g.
///
/// ```ignore
/// // `U: OtherTrait` is required, `Self: Sized` is implied.
/// trait Trait<U: OtherTrait>: Sized {
///     // `T: Clone` is required, `Self::Type<T>: Debug` is implied.
///     type Type<T: Clone>: Debug;
/// }
/// ```
///
/// If `add_drop` is true, we add a `T: Drop` bound for every type generic.
pub fn required_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    add_drop: bool,
) -> GenericPredicates<'tcx> {
    use DefKind::*;
    let def_kind = tcx.def_kind(def_id);
    let mut predicates = match def_kind {
        AssocConst
        | AssocFn
        | AssocTy
        | Const
        | Enum
        | Fn
        | ForeignTy
        | Impl { .. }
        | OpaqueTy
        | Static { .. }
        | Struct
        | TyAlias
        | Union => predicates_defined_on(tcx, def_id),
        // We consider all predicates on traits to be outputs
        Trait | TraitAlias => Default::default(),
        // `predicates_defined_on` ICEs on other def kinds.
        _ => Default::default(),
    };
    if add_drop {
        // Add a `T: Drop` bound for every generic, unless the current trait is `Drop` itself, or
        // `Sized`.
        let drop_trait = tcx.lang_items().drop_trait().unwrap();
        let sized_trait = tcx.lang_items().sized_trait().unwrap();
        if def_id != drop_trait && def_id != sized_trait {
            let extra_bounds = tcx
                .generics_of(def_id)
                .own_params
                .iter()
                .filter(|param| matches!(param.kind, GenericParamDefKind::Type { .. }))
                .map(|param| tcx.mk_param_from_def(param))
                .map(|ty| Binder::dummy(TraitRef::new(tcx, drop_trait, [ty])))
                .map(|tref| tref.upcast(tcx))
                .map(|clause| (clause, DUMMY_SP));
            predicates.predicates = tcx
                .arena
                .alloc_from_iter(predicates.predicates.iter().copied().chain(extra_bounds));
        }
    }
    predicates
}

/// The special "self" predicate on a trait.
pub fn self_predicate<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> PolyTraitRef<'tcx> {
    // Copied from the code of `tcx.predicates_of()`.
    Binder::dummy(TraitRef::identity(tcx, def_id))
}

/// The predicates that can be deduced from the presence of this item in a signature. We only
/// consider predicates implied by traits here, not implied bounds such as `&'a T` implying `T:
/// 'a`. E.g.
///
/// ```ignore
/// // `U: OtherTrait` is required, `Self: Sized` is implied.
/// trait Trait<U: OtherTrait>: Sized {
///     // `T: Clone` is required, `Self::Type<T>: Debug` is implied.
///     type Type<T: Clone>: Debug;
/// }
/// ```
///
/// If `add_drop` is true, we add a `T: Drop` bound for every type generic and associated type.
pub fn implied_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    add_drop: bool,
) -> GenericPredicates<'tcx> {
    use DefKind::*;
    let parent = tcx.opt_parent(def_id);
    match tcx.def_kind(def_id) {
        // We consider all predicates on traits to be outputs
        Trait | TraitAlias => predicates_defined_on(tcx, def_id),
        AssocTy if matches!(tcx.def_kind(parent.unwrap()), Trait) => {
            let mut predicates = GenericPredicates {
                parent,
                // `skip_binder` is for the GAT `EarlyBinder`
                predicates: tcx.explicit_item_bounds(def_id).skip_binder(),
                ..GenericPredicates::default()
            };
            if add_drop {
                // Add a `Drop` bound to the assoc item.
                let drop_trait = tcx.lang_items().drop_trait().unwrap();
                let ty =
                    Ty::new_projection(tcx, def_id, GenericArgs::identity_for_item(tcx, def_id));
                let tref = Binder::dummy(TraitRef::new(tcx, drop_trait, [ty]));
                predicates.predicates = tcx.arena.alloc_from_iter(
                    predicates
                        .predicates
                        .iter()
                        .copied()
                        .chain([(tref.upcast(tcx), DUMMY_SP)]),
                );
            }
            predicates
        }
        _ => GenericPredicates::default(),
    }
}

/// Erase all regions. Largely copied from `tcx.erase_regions`.
pub fn erase_all_regions<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>>,
{
    use rustc_middle::ty;
    struct RegionEraserVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for RegionEraserVisitor<'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
            ty.super_fold_with(self)
        }

        fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
        where
            T: TypeFoldable<TyCtxt<'tcx>>,
        {
            // Empty the binder
            Binder::dummy(t.skip_binder().fold_with(self))
        }

        fn fold_region(&mut self, _r: ty::Region<'tcx>) -> ty::Region<'tcx> {
            // We erase bound regions despite it being possibly incorrect. `for<'a> fn(&'a
            // ())` and `fn(&'free ())` are different types: they may implement different
            // traits and have a different `TypeId`. It's unclear whether this can cause us
            // to select the wrong trait reference.
            self.tcx.lifetimes.re_erased
        }
    }
    value.fold_with(&mut RegionEraserVisitor { tcx })
}

// Lifetimes are irrelevant when resolving instances.
pub fn erase_and_norm<'tcx, T>(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, x: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>> + Copy,
{
    erase_all_regions(
        tcx,
        tcx.try_normalize_erasing_regions(typing_env, x)
            .unwrap_or(x),
    )
}

pub trait ToPolyTraitRef<'tcx> {
    fn to_poly_trait_ref(&self) -> PolyTraitRef<'tcx>;
}

impl<'tcx> ToPolyTraitRef<'tcx> for PolyTraitPredicate<'tcx> {
    fn to_poly_trait_ref(&self) -> PolyTraitRef<'tcx> {
        self.map_bound_ref(|trait_pred| trait_pred.trait_ref)
    }
}
