use crate::prelude::*;

#[cfg(feature = "rustc")]
pub mod resolution;
#[cfg(feature = "rustc")]
mod utils;
#[cfg(feature = "rustc")]
pub use utils::{
    Predicates, ToPolyTraitRef, erase_and_norm, erase_free_regions, implied_predicates, normalize,
    predicates_defined_on, required_predicates, self_predicate,
};

#[cfg(feature = "rustc")]
pub use resolution::PredicateSearcher;
#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

#[cfg(feature = "rustc")]
pub use utils::is_sized_related_trait;

#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprPathChunk {
    AssocItem {
        /// Reference to the item, with generics (for GATs), e.g. the `T` and `T: Clone` `ImplExpr`
        /// in the following example:
        /// ```ignore
        /// trait Foo {
        ///     type Type<T: Clone>: Debug;
        /// }
        /// ```
        item: ItemRef,
        assoc_item: AssocItem,
        /// The implemented predicate.
        predicate: Binder<TraitPredicate>,
        predicate_id: PredicateId,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
    Parent {
        /// The implemented predicate.
        predicate: Binder<TraitPredicate>,
        predicate_id: PredicateId,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ImplExprPathChunk> for resolution::PathChunk<'tcx> {
    fn sinto(&self, s: &S) -> ImplExprPathChunk {
        match self {
            resolution::PathChunk::AssocItem {
                item,
                generic_args,
                predicate,
                index,
                ..
            } => ImplExprPathChunk::AssocItem {
                item: translate_item_ref(s, item.def_id, generic_args),
                assoc_item: AssocItem::sfrom(s, item),
                predicate: predicate.sinto(s),
                predicate_id: <_ as SInto<_, Clause>>::sinto(predicate, s).id,
                index: index.sinto(s),
            },
            resolution::PathChunk::Parent {
                predicate, index, ..
            } => ImplExprPathChunk::Parent {
                predicate: predicate.sinto(s),
                predicate_id: <_ as SInto<_, Clause>>::sinto(predicate, s).id,
                index: index.sinto(s),
            },
        }
    }
}

/// The source of a particular trait implementation. Most often this is either `Concrete` for a
/// concrete `impl Trait for Type {}` item, or `LocalBound` for a context-bound `where T: Trait`.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::ImplExprAtom<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprAtom {
    /// A concrete `impl Trait for Type {}` item.
    #[custom_arm(FROM_TYPE::Concrete { def_id, generics } => TO_TYPE::Concrete(
        translate_item_ref(s, *def_id, generics),
    ),)]
    Concrete(ItemRef),
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        #[not_in_source]
        #[value({
            let Self::LocalBound { predicate, .. } = self else { unreachable!() };
            predicate.sinto(s).id
        })]
        predicate_id: PredicateId,
        /// The nth (non-self) predicate found for this item. We use predicates from
        /// `required_predicates` starting from the parentmost item.
        index: usize,
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// The implicit `Self: Trait` clause present inside a `trait Trait {}` item.
    // TODO: should we also get that clause for trait impls?
    SelfImpl {
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `FnMut`. This
    /// morally points to an invisible `impl` block; as such it contains the information we may
    /// need from one.
    Builtin {
        /// Extra data for the given trait.
        trait_data: BuiltinTraitData,
        /// The `ImplExpr`s required to satisfy the implied predicates on the trait declaration.
        /// E.g. since `FnMut: FnOnce`, a built-in `T: FnMut` impl would have an `ImplExpr` for `T:
        /// FnOnce`.
        impl_exprs: Vec<ImplExpr>,
        /// The values of the associated types for this trait.
        types: Vec<(DefId, Ty, Vec<ImplExpr>)>,
    },
    /// An error happened while resolving traits.
    Error(String),
}

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::BuiltinTraitData<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum BuiltinTraitData {
    /// A virtual `Drop` implementation.
    /// `Drop` doesn't work like a real trait but we want to pretend it does. If a type has a
    /// user-defined `impl Drop for X` we just use the `Concrete` variant, but if it doesn't we use
    /// this variant to supply the data needed to know what code will run on drop.
    Drop(DropData),
    /// Some other builtin trait.
    Other,
}

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::DropData<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum DropData {
    /// A drop that does nothing, e.g. for scalars and pointers.
    Noop,
    /// An implicit `Drop` local clause, if the `resolve_drop_bounds` option is `false`. If that
    /// option is `true`, we'll add `Drop` bounds to every type param, and use that to resolve
    /// `Drop` impls of generics. If it's `false`, we use this variant to indicate that the drop
    /// clause comes from a generic or associated type.
    Implicit,
    /// The implicit `Drop` impl that exists for every type without an explicit `Drop` impl. The
    /// virtual impl is considered to have one `T: Drop` bound for each generic argument of the
    /// target type; it then simply drops each field in order.
    Glue {
        /// The type we're generating glue for.
        ty: Ty,
        /// The `ImplExpr`s for the `T: Drop` bounds of the virtual impl. There is one for each
        /// generic argument, in order.
        impl_exprs: Vec<ImplExpr>,
    },
}

/// An `ImplExpr` describes the full data of a trait implementation. Because of generics, this may
/// need to combine several concrete trait implementation items. For example, `((1u8, 2u8),
/// "hello").clone()` combines the generic implementation of `Clone` for `(A, B)` with the
/// concrete implementations for `u8` and `&str`, represented as a tree.
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema, AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::ImplExpr<'tcx>, state: S as s)]
pub struct ImplExpr {
    /// The trait this is an impl for.
    pub r#trait: Binder<TraitRef>,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom,
}

/// Given a clause `clause` in the context of some impl block `impl_did`, susbts correctly `Self`
/// from `clause` and (1) derive a `Clause` and (2) resolve an `ImplExpr`.
#[cfg(feature = "rustc")]
pub fn super_clause_to_clause_and_impl_expr<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    impl_did: rustc_span::def_id::DefId,
    clause: rustc_middle::ty::Clause<'tcx>,
    span: rustc_span::Span,
) -> Option<(Clause, ImplExpr, Span)> {
    let tcx = s.base().tcx;
    let impl_trait_ref = tcx
        .impl_trait_ref(impl_did)
        .map(|binder| rustc_middle::ty::Binder::dummy(binder.instantiate_identity()))?;
    let original_predicate_id = {
        // We don't want the id of the substituted clause id, but the
        // original clause id (with, i.e., `Self`)
        let s = &s.with_owner_id(impl_trait_ref.def_id());
        clause.sinto(s).id
    };
    let new_clause = clause.instantiate_supertrait(tcx, impl_trait_ref);
    let impl_expr = solve_trait(
        s,
        new_clause
            .as_predicate()
            .as_trait_clause()?
            .to_poly_trait_ref(),
    );
    let mut new_clause_no_binder = new_clause.sinto(s);
    new_clause_no_binder.id = original_predicate_id;
    Some((new_clause_no_binder, impl_expr, span.sinto(s)))
}

/// This is the entrypoint of the solving.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s))]
pub fn solve_trait<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplExpr {
    let warn = |msg: &str| {
        if !s.base().ty_alias_mode {
            crate::warning!(s, "{}", msg)
        }
    };
    if let Some(impl_expr) = s.with_cache(|cache| cache.impl_exprs.get(&trait_ref).cloned()) {
        return impl_expr;
    }
    let resolved =
        s.with_predicate_searcher(|pred_searcher| pred_searcher.resolve(&trait_ref, &warn));
    let impl_expr = match resolved {
        Ok(x) => x.sinto(s),
        Err(e) => crate::fatal!(s, "{}", e),
    };
    s.with_cache(|cache| cache.impl_exprs.insert(trait_ref, impl_expr.clone()));
    impl_expr
}

/// Translate a reference to an item, resolving the appropriate trait clauses as needed.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn translate_item_ref<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> ItemRef {
    ItemRef::translate(s, def_id, generics)
}

/// Solve the trait obligations for a specific item use (for example, a method call, an ADT, etc.)
/// in the current context. Just like generic args include generics of parent items, this includes
/// impl exprs for parent items.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_required_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<ImplExpr> {
    fn accumulate<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def_id: RDefId,
        generics: ty::GenericArgsRef<'tcx>,
        impl_exprs: &mut Vec<ImplExpr>,
    ) {
        let tcx = s.base().tcx;
        use rustc_hir::def::DefKind::*;
        match tcx.def_kind(def_id) {
            AssocTy | AssocFn | AssocConst | Closure | Ctor(..) | Variant => {
                let parent = tcx.parent(def_id);
                accumulate(s, parent, generics, impl_exprs);
            }
            _ => {}
        }
        let predicates = required_predicates(tcx, def_id, s.base().options.bounds_options);
        impl_exprs.extend(solve_item_traits_inner(s, generics, predicates));
    }
    let mut impl_exprs = vec![];
    accumulate(s, def_id, generics, &mut impl_exprs);
    impl_exprs
}

/// Solve the trait obligations for implementing a trait (or for trait associated type bounds) in
/// the current context.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_implied_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<ImplExpr> {
    let predicates = implied_predicates(s.base().tcx, def_id, s.base().options.bounds_options);
    solve_item_traits_inner(s, generics, predicates)
}

/// Apply the given generics to the provided clauses and resolve the trait references in the
/// current context.
#[cfg(feature = "rustc")]
fn solve_item_traits_inner<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    generics: ty::GenericArgsRef<'tcx>,
    predicates: utils::Predicates<'tcx>,
) -> Vec<ImplExpr> {
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    predicates
        .iter()
        .map(|(clause, _span)| *clause)
        .filter_map(|clause| clause.as_trait_clause())
        .map(|clause| clause.to_poly_trait_ref())
        // Substitute the item generics
        .map(|trait_ref| ty::EarlyBinder::bind(trait_ref).instantiate(tcx, generics))
        // We unfortunately don't have a way to normalize without erasing regions.
        .map(|trait_ref| {
            tcx.try_normalize_erasing_regions(typing_env, trait_ref)
                .unwrap_or(trait_ref)
        })
        // Resolve
        .map(|trait_ref| solve_trait(s, trait_ref))
        .collect()
}

/// Retrieve the `Self: Trait` clause for a trait associated item.
#[cfg(feature = "rustc")]
pub fn self_clause_for_item<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<ImplExpr> {
    let tcx = s.base().tcx;

    let tr_def_id = tcx.trait_of_item(def_id)?;
    // The "self" predicate in the context of the trait.
    let self_pred = self_predicate(tcx, tr_def_id);
    // Substitute to be in the context of the current item.
    let generics = generics.truncate_to(tcx, tcx.generics_of(tr_def_id));
    let self_pred = ty::EarlyBinder::bind(self_pred).instantiate(tcx, generics);

    // Resolve
    Some(solve_trait(s, self_pred))
}
