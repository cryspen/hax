//! Copies of the relevant type-level types. These are semantically-rich representations of
//! type-level concepts such as types and trait references.
use crate::prelude::*;
use crate::sinto_as_usize;
use crate::sinto_todo;
use std::sync::Arc;

#[cfg(feature = "rustc")]
use rustc_middle::ty;

/// Generic container for decorating items with a type, a span,
/// attributes and other meta-data.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Decorated<T> {
    pub ty: Ty,
    pub span: Span,
    pub contents: Box<T>,
    pub hir_id: Option<(usize, usize)>,
    pub attributes: Vec<Attribute>,
}

/// Reflects [`rustc_middle::infer::canonical::CanonicalTyVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalTyVarKind, state: S as gstate)]
pub enum CanonicalTyVarKind {
    General(UniverseIndex),
    Int,
    Float,
}

sinto_as_usize!(rustc_middle::ty, UniverseIndex);

/// Reflects [`ty::ParamTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ParamTy, state: S as gstate)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`ty::ParamConst`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: ty::ParamConst, state: S as gstate)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

/// A predicate without `Self`, for use in `dyn Trait`.
///
/// Reflects [`ty::ExistentialPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ExistentialPredicate<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExistentialPredicate {
    /// E.g. `From<u64>`. Note that this isn't `T: From<u64>` with a given `T`, this is just
    /// `From<u64>`. Could be written `?: From<u64>`.
    Trait(ExistentialTraitRef),
    /// E.g. `Iterator::Item = u64`. Could be written `<? as Iterator>::Item = u64`.
    Projection(ExistentialProjection),
    /// E.g. `Send`.
    AutoTrait(DefId),
}

/// Reflects [`rustc_type_ir::ExistentialTraitRef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialTraitRef<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
}

/// Reflects [`rustc_type_ir::ExistentialProjection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialProjection<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
    pub term: Term,
}

/// Reflects [`ty::DynKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: ty::DynKind, state: S as _s)]
pub enum DynKind {
    Dyn,
    DynStar,
}

/// Reflects [`ty::BoundTyKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundTyKind, state: S as gstate)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

/// Reflects [`ty::BoundTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundTy, state: S as gstate)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

sinto_as_usize!(rustc_middle::ty, BoundVar);

/// Reflects [`ty::BoundRegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundRegionKind, state: S as gstate)]
pub enum BoundRegionKind {
    Anon,
    Named(DefId, Symbol),
    ClosureEnv,
}

/// Reflects [`ty::BoundRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundRegion, state: S as gstate)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

/// Reflects [`ty::PlaceholderRegion`]
pub type PlaceholderRegion = Placeholder<BoundRegion>;
/// Reflects [`ty::PlaceholderConst`]
pub type PlaceholderConst = Placeholder<BoundVar>;
/// Reflects [`ty::PlaceholderType`]
pub type PlaceholderType = Placeholder<BoundTy>;

/// Reflects [`ty::Placeholder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Placeholder<U>>
    for ty::Placeholder<T>
{
    fn sinto(&self, s: &S) -> Placeholder<U> {
        Placeholder {
            universe: self.universe.sinto(s),
            bound: self.bound.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::Canonical`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Canonical<T> {
    pub max_universe: UniverseIndex,
    pub variables: Vec<CanonicalVarInfo>,
    pub value: T,
}
/// Reflects [`ty::CanonicalUserType`]
pub type CanonicalUserType = Canonical<UserType>;

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
    for rustc_middle::infer::canonical::Canonical<'tcx, T>
{
    fn sinto(&self, s: &S) -> Canonical<U> {
        Canonical {
            max_universe: self.max_universe.sinto(s),
            variables: self.variables.sinto(s),
            value: self.value.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::CanonicalVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalVarKind<'tcx>, state: S as gstate)]
pub enum CanonicalVarInfo {
    Ty(CanonicalTyVarKind),
    PlaceholderTy(PlaceholderType),
    Region(UniverseIndex),
    PlaceholderRegion(PlaceholderRegion),
    Const(UniverseIndex),
    PlaceholderConst(PlaceholderConst),
}

/// Reflects [`ty::UserSelfTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy {
    pub impl_def_id: DefId,
    pub self_ty: Ty,
}

/// Reflects [`ty::UserArgs`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::UserArgs<'tcx>, state: S as gstate)]
pub struct UserArgs {
    pub args: Vec<GenericArg>,
    pub user_self_ty: Option<UserSelfTy>,
}

/// Reflects [`ty::UserType`]: this is currently
/// disabled, and everything is printed as debug in the
/// [`UserType::Todo`] variant.
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::UserType<'tcx>, state: S as _s)]
pub enum UserType {
    // TODO: for now, we don't use user types at all.
    // We disable it for now, since it cause the following to fail:
    //
    //    pub const MY_VAL: u16 = 5;
    //    pub type Alias = MyStruct<MY_VAL>; // Using the literal 5, it goes through
    //
    //    pub struct MyStruct<const VAL: u16> {}
    //
    //    impl<const VAL: u16> MyStruct<VAL> {
    //        pub const MY_CONST: u16 = VAL;
    //    }
    //
    //    pub fn do_something() -> u32 {
    //        u32::from(Alias::MY_CONST)
    //    }
    //
    // In this case, we get a [ty::ConstKind::Bound] in
    // [do_something], which we are not able to translate.
    // See: https://github.com/hacspec/hax/pull/209

    // Ty(Ty),
    // TypeOf(DefId, UserArgs),
    #[todo]
    Todo(String),
}

/// Reflects [`ty::VariantDiscr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::VariantDiscr, state: S as gstate)]
pub enum DiscriminantDefinition {
    Explicit(DefId),
    Relative(u32),
}

/// Reflects [`ty::util::Discr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::util::Discr<'tcx>, state: S as gstate)]
pub struct DiscriminantValue {
    pub val: u128,
    pub ty: Ty,
}

/// Reflects [`ty::Visibility`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Visibility<Id> {
    Public,
    Restricted(Id),
}

#[cfg(feature = "rustc")]
impl<S, T: SInto<S, U>, U> SInto<S, Visibility<U>> for ty::Visibility<T> {
    fn sinto(&self, s: &S) -> Visibility<U> {
        use ty::Visibility as T;
        match self {
            T::Public => Visibility::Public,
            T::Restricted(id) => Visibility::Restricted(id.sinto(s)),
        }
    }
}

/// Reflects [`ty::FieldDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FieldDef {
    pub did: DefId,
    /// Field definition of [tuple
    /// structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types)
    /// are anonymous, in that case `name` is [`None`].
    pub name: Option<Symbol>,
    pub vis: Visibility<DefId>,
    pub ty: Ty,
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, FieldDef> for ty::FieldDef {
    fn sinto(&self, s: &S) -> FieldDef {
        let tcx = s.base().tcx;
        let ty = {
            let generics = ty::GenericArgs::identity_for_item(tcx, self.did);
            self.ty(tcx, generics).sinto(s)
        };
        let name = {
            let name = self.name.sinto(s);
            let is_user_provided = {
                // SH: Note that the only way I found of checking if the user wrote the name or if it
                // is just an integer generated by rustc is by checking if it is just made of
                // numerals...
                name.parse::<usize>().is_err()
            };
            is_user_provided.then_some(name)
        };

        FieldDef {
            did: self.did.sinto(s),
            name,
            vis: self.vis.sinto(s),
            ty,
            span: tcx.def_span(self.did).sinto(s),
        }
    }
}

/// Reflects [`ty::VariantDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct VariantDef {
    pub def_id: DefId,
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr_def: DiscriminantDefinition,
    pub discr_val: DiscriminantValue,
    /// The definitions of the fields on this variant. In case of [tuple
    /// structs/variants](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types),
    /// the fields are anonymous, otherwise fields are named.
    pub fields: IndexVec<FieldIdx, FieldDef>,
    /// Span of the definition of the variant
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl VariantDef {
    fn sfrom<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def: &ty::VariantDef,
        discr_val: ty::util::Discr<'tcx>,
    ) -> Self {
        VariantDef {
            def_id: def.def_id.sinto(s),
            ctor: def.ctor.sinto(s),
            name: def.name.sinto(s),
            discr_def: def.discr.sinto(s),
            discr_val: discr_val.sinto(s),
            fields: def.fields.sinto(s),
            span: s.base().tcx.def_span(def.def_id).sinto(s),
        }
    }
}

/// Reflects [`ty::EarlyParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::EarlyParamRegion, state: S as gstate)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`ty::LateParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::LateParamRegion, state: S as gstate)]
pub struct LateParamRegion {
    pub scope: DefId,
    pub kind: LateParamRegionKind,
}

/// Reflects [`ty::LateParamRegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::LateParamRegionKind, state: S as gstate)]
pub enum LateParamRegionKind {
    Anon(u32),
    Named(DefId, Symbol),
    ClosureEnv,
}

/// Reflects [`ty::RegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::RegionKind<'tcx>, state: S as gstate)]
pub enum RegionKind {
    ReEarlyParam(EarlyParamRegion),
    ReBound(DebruijnIndex, BoundRegion),
    ReLateParam(LateParamRegion),
    ReStatic,
    ReVar(RegionVid),
    RePlaceholder(PlaceholderRegion),
    ReErased,
    ReError(ErrorGuaranteed),
}

sinto_as_usize!(rustc_middle::ty, DebruijnIndex);
sinto_as_usize!(rustc_middle::ty, RegionVid);

/// Reflects [`ty::Region`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::Region<'tcx>, state: S as s)]
pub struct Region {
    #[value(self.kind().sinto(s))]
    pub kind: RegionKind,
}

/// Reflects both [`ty::GenericArg`] and [`ty::GenericArgKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::GenericArgKind<'tcx>, state: S as s)]
pub enum GenericArg {
    Lifetime(Region),
    Type(Ty),
    Const(ConstantExpr),
}

/// Contents of `ItemRef`.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ItemRefContents {
    /// The item being refered to.
    pub def_id: DefId,
    /// The generics passed to the item. If `in_trait` is `Some`, these are only the generics of
    /// the method/type/const itself; generics for the traits are available in
    /// `in_trait.unwrap().trait`.
    pub generic_args: Vec<GenericArg>,
    /// Witnesses of the trait clauses required by the item, e.g. `T: Sized` for `Option<T>` or `B:
    /// ToOwned` for `Cow<'a, B>`. Same as above, for associated items this only includes clauses
    /// for the item itself.
    pub impl_exprs: Vec<ImplExpr>,
    /// If we're referring to a trait associated item, this gives the trait clause/impl we're
    /// referring to.
    pub in_trait: Option<ImplExpr>,
}

/// Reference to an item, with generics. Basically any mention of an item (function, type, etc)
/// uses this.
///
/// This can refer to a top-level item or to a trait associated item. Example:
/// ```ignore
/// trait MyTrait<TraitType, const TraitConst: usize> {
///   fn meth<MethType>(...) {...}
/// }
/// fn example_call<TraitType, SelfType: MyTrait<TraitType, 12>>(x: SelfType) {
///   x.meth::<String>(...)
/// }
/// ```
/// Here, in the call `x.meth::<String>(...)` we will build an `ItemRef` that looks like:
/// ```ignore
/// ItemRef {
///     def_id = MyTrait::meth,
///     generic_args = [String],
///     impl_exprs = [<proof of `String: Sized`>],
///     in_trait = Some(<proof of `SelfType: MyTrait<TraitType, 12>`>,
/// }
/// ```
/// The `in_trait` `ImplExpr` will have in its `trait` field a representation of the `SelfType:
/// MyTrait<TraitType, 12>` predicate, which looks like:
/// ```ignore
/// ItemRef {
///     def_id = MyTrait,
///     generic_args = [SelfType, TraitType, 12],
///     impl_exprs = [],
///     in_trait = None,
/// }
/// ```
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
pub struct ItemRef {
    pub(crate) contents: id_table::Node<ItemRefContents>,
}

impl ItemRefContents {
    #[cfg(feature = "rustc")]
    pub fn intern<'tcx, S: BaseState<'tcx>>(self, s: &S) -> ItemRef {
        s.with_global_cache(|cache| {
            let table_session = &mut cache.id_table_session;
            let contents = id_table::Node::new(self, table_session);
            ItemRef { contents }
        })
    }
}

impl ItemRef {
    #[cfg(feature = "rustc")]
    pub fn new<'tcx, S: BaseState<'tcx>>(
        s: &S,
        def_id: DefId,
        generic_args: Vec<GenericArg>,
        impl_exprs: Vec<ImplExpr>,
        in_trait: Option<ImplExpr>,
    ) -> ItemRef {
        let contents = ItemRefContents {
            def_id,
            generic_args,
            impl_exprs,
            in_trait,
        };
        contents.intern(s)
    }

    pub fn contents(&self) -> &ItemRefContents {
        &self.contents
    }

    #[cfg(feature = "rustc")]
    pub fn mutate<'tcx, S: BaseState<'tcx>>(
        &mut self,
        s: &S,
        f: impl FnOnce(&mut ItemRefContents),
    ) {
        let mut contents = self.contents().clone();
        f(&mut contents);
        *self = contents.intern(s);
    }
}

impl std::ops::Deref for ItemRef {
    type Target = ItemRefContents;
    fn deref(&self) -> &Self::Target {
        self.contents()
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericArg> for ty::GenericArg<'tcx> {
    fn sinto(&self, s: &S) -> GenericArg {
        self.unpack().sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Vec<GenericArg>> for ty::GenericArgsRef<'tcx> {
    fn sinto(&self, s: &S) -> Vec<GenericArg> {
        self.iter().map(|v| v.unpack().sinto(s)).collect()
    }
}

/// Reflects both [`ty::GenericArg`] and [`ty::GenericArgKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitIntType, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

/// Reflects partially [`ty::InferTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: ty::InferTy, state: S as gstate)]
pub enum InferTy {
    #[custom_arm(FROM_TYPE::TyVar(..) => TO_TYPE::TyVar,)]
    TyVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::IntVar(..) => TO_TYPE::IntVar,)]
    IntVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::FloatVar(..) => TO_TYPE::FloatVar,)]
    FloatVar, /*TODO?*/
    FreshTy(u32),
    FreshIntTy(u32),
    FreshFloatTy(u32),
}

/// Reflects [`rustc_type_ir::IntTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::IntTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

/// Reflects [`rustc_type_ir::FloatTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::FloatTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, FloatTy> for rustc_ast::ast::FloatTy {
    fn sinto(&self, _: &S) -> FloatTy {
        use rustc_ast::ast::FloatTy as T;
        match self {
            T::F16 => FloatTy::F16,
            T::F32 => FloatTy::F32,
            T::F64 => FloatTy::F64,
            T::F128 => FloatTy::F128,
        }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, IntTy> for rustc_ast::ast::IntTy {
    fn sinto(&self, _: &S) -> IntTy {
        use rustc_ast::ast::IntTy as T;
        match self {
            T::Isize => IntTy::Isize,
            T::I8 => IntTy::I8,
            T::I16 => IntTy::I16,
            T::I32 => IntTy::I32,
            T::I64 => IntTy::I64,
            T::I128 => IntTy::I128,
        }
    }
}
#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, UintTy> for rustc_ast::ast::UintTy {
    fn sinto(&self, _: &S) -> UintTy {
        use rustc_ast::ast::UintTy as T;
        match self {
            T::Usize => UintTy::Usize,
            T::U8 => UintTy::U8,
            T::U16 => UintTy::U16,
            T::U32 => UintTy::U32,
            T::U64 => UintTy::U64,
            T::U128 => UintTy::U128,
        }
    }
}

/// Reflects [`rustc_type_ir::UintTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::UintTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl ToString for IntTy {
    fn to_string(&self) -> String {
        use IntTy::*;
        match self {
            Isize => "isize".to_string(),
            I8 => "i8".to_string(),
            I16 => "i16".to_string(),
            I32 => "i32".to_string(),
            I64 => "i64".to_string(),
            I128 => "i128".to_string(),
        }
    }
}

impl ToString for UintTy {
    fn to_string(&self) -> String {
        use UintTy::*;
        match self {
            Usize => "usize".to_string(),
            U8 => "u8".to_string(),
            U16 => "u16".to_string(),
            U32 => "u32".to_string(),
            U64 => "u64".to_string(),
            U128 => "u128".to_string(),
        }
    }
}

/// Reflects [`ty::TypeAndMut`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::TypeAndMut<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeAndMut {
    pub ty: Box<Ty>,
    pub mutbl: Mutability,
}

#[cfg(feature = "rustc")]
impl<S, U, T: SInto<S, U>> SInto<S, Vec<U>> for ty::List<T> {
    fn sinto(&self, s: &S) -> Vec<U> {
        self.iter().map(|x| x.sinto(s)).collect()
    }
}

/// Reflects [`ty::GenericParamDef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::GenericParamDef, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct GenericParamDef {
    pub name: Symbol,
    pub def_id: DefId,
    pub index: u32,
    pub pure_wrt_drop: bool,
    #[value(
        match self.kind {
            ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
            ty::GenericParamDefKind::Type { has_default, synthetic } => GenericParamDefKind::Type { has_default, synthetic },
            ty::GenericParamDefKind::Const { has_default, .. } => {
                let ty = s.base().tcx.type_of(self.def_id).instantiate_identity().sinto(s);
                GenericParamDefKind::Const { has_default, ty }
            },
        }
    )]
    pub kind: GenericParamDefKind,
}

/// Reflects [`ty::GenericParamDefKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum GenericParamDefKind {
    Lifetime,
    Type { has_default: bool, synthetic: bool },
    Const { has_default: bool, ty: Ty },
}

/// Reflects [`ty::Generics`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::Generics, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct TyGenerics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    #[from(own_params)]
    pub params: Vec<GenericParamDef>,
    // pub param_def_id_to_index: FxHashMap<DefId, u32>,
    pub has_self: bool,
    pub has_late_bound_regions: Option<Span>,
}

#[cfg(feature = "rustc")]
impl TyGenerics {
    pub(crate) fn count_total_params(&self) -> usize {
        self.parent_count + self.params.len()
    }
}

/// This type merges the information from
/// `rustc_type_ir::AliasKind` and `ty::AliasTy`
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Alias {
    pub kind: AliasKind,
    pub args: Vec<GenericArg>,
    pub def_id: DefId,
}

/// Reflects [`ty::AliasKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasKind {
    /// The projection of a trait type: `<Ty as Trait<...>>::Type<...>`
    Projection {
        /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
        impl_expr: ImplExpr,
        /// The `Type` in `Ty: Trait<..., Type = U>`.
        assoc_item: AssocItem,
    },
    /// An associated type in an inherent impl.
    Inherent,
    /// An `impl Trait` opaque type.
    Opaque {
        /// The real type hidden inside this opaque type.
        hidden_ty: Ty,
    },
    /// A type alias that references opaque types. Likely to always be normalized away.
    Free,
}

#[cfg(feature = "rustc")]
impl Alias {
    #[tracing::instrument(level = "trace", skip(s))]
    fn from<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        alias_kind: &rustc_type_ir::AliasTyKind,
        alias_ty: &ty::AliasTy<'tcx>,
    ) -> TyKind {
        let tcx = s.base().tcx;
        use rustc_type_ir::AliasTyKind as RustAliasKind;
        let kind = match alias_kind {
            RustAliasKind::Projection => {
                let trait_ref = alias_ty.trait_ref(tcx);
                // In a case like:
                // ```
                // impl<T, U> Trait for Result<T, U>
                // where
                //     for<'a> &'a Result<T, U>: IntoIterator,
                //     for<'a> <&'a Result<T, U> as IntoIterator>::Item: Copy,
                // {}
                // ```
                // the `&'a Result<T, U> as IntoIterator` trait ref has escaping bound variables
                // yet we dont have a binder around (could even be several). Binding this correctly
                // is therefore difficult. Since our trait resolution ignores lifetimes anyway, we
                // just erase them. See also https://github.com/hacspec/hax/issues/747.
                let trait_ref = crate::traits::erase_and_norm(tcx, s.typing_env(), trait_ref);
                AliasKind::Projection {
                    assoc_item: tcx.associated_item(alias_ty.def_id).sinto(s),
                    impl_expr: solve_trait(s, ty::Binder::dummy(trait_ref)),
                }
            }
            RustAliasKind::Inherent => AliasKind::Inherent,
            RustAliasKind::Opaque => {
                // Reveal the underlying `impl Trait` type.
                let ty = tcx.type_of(alias_ty.def_id).instantiate(tcx, alias_ty.args);
                AliasKind::Opaque {
                    hidden_ty: ty.sinto(s),
                }
            }
            RustAliasKind::Free => AliasKind::Free,
        };
        TyKind::Alias(Alias {
            kind,
            args: alias_ty.args.sinto(s),
            def_id: alias_ty.def_id.sinto(s),
        })
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Box<Ty>> for ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Box<Ty> {
        Box::new(self.sinto(s))
    }
}

/// Reflects [`rustc_middle::ty::Ty`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
pub struct Ty {
    pub(crate) kind: id_table::Node<TyKind>,
}

impl Ty {
    #[cfg(feature = "rustc")]
    pub fn new<'tcx, S: BaseState<'tcx>>(s: &S, kind: TyKind) -> Self {
        s.with_global_cache(|cache| {
            let table_session = &mut cache.id_table_session;
            let kind = id_table::Node::new(kind, table_session);
            Ty { kind }
        })
    }

    pub fn inner(&self) -> &Arc<TyKind> {
        self.kind.inner()
    }

    pub fn kind(&self) -> &TyKind {
        self.inner().as_ref()
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Ty {
        if let Some(ty) = s.with_cache(|cache| cache.tys.get(self).cloned()) {
            return ty;
        }
        let kind: TyKind = self.kind().sinto(s);
        let ty = Ty::new(s, kind);
        s.with_cache(|cache| {
            cache.tys.insert(*self, ty.clone());
        });
        ty
    }
}

/// Reflects [`ty::TyKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::TyKind<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),

    #[custom_arm(
        ty::TyKind::FnDef(fun_id, generics) => {
            let item = translate_item_ref(s, *fun_id, generics);
            let tcx = s.base().tcx;
            let fn_sig = tcx.fn_sig(*fun_id).instantiate(tcx, generics);
            let fn_sig = Box::new(fn_sig.sinto(s));
            TyKind::FnDef { item, fn_sig }
        },
    )]
    /// Reflects [`ty::TyKind::FnDef`]
    FnDef {
        item: ItemRef,
        fn_sig: Box<PolyFnSig>,
    },

    #[custom_arm(
        ty::TyKind::FnPtr(tys, header) => {
            let sig = tys.map_bound(|tys| ty::FnSig {
                inputs_and_output: tys.inputs_and_output,
                c_variadic: header.c_variadic,
                safety: header.safety,
                abi: header.abi,
            });
            TyKind::Arrow(Box::new(sig.sinto(s)))
        },
    )]
    /// Reflects [`ty::TyKind::FnPtr`]
    Arrow(Box<PolyFnSig>),

    #[custom_arm(
        ty::TyKind::Closure (def_id, generics) => {
            let closure = generics.as_closure();
            TyKind::Closure(ClosureArgs::sfrom(s, *def_id, closure))
        },
    )]
    Closure(ClosureArgs),

    #[custom_arm(FROM_TYPE::Adt(adt_def, generics) => TO_TYPE::Adt(translate_item_ref(s, adt_def.did(), generics)),)]
    Adt(ItemRef),
    #[custom_arm(FROM_TYPE::Foreign(def_id) => TO_TYPE::Foreign(ItemRef::new(s, def_id.sinto(s), vec![], vec![], None)),)]
    Foreign(ItemRef),
    Str,
    Array(Box<Ty>, #[map(Box::new(x.sinto(s)))] Box<ConstantExpr>),
    Slice(Box<Ty>),
    RawPtr(Box<Ty>, Mutability),
    Ref(Region, Box<Ty>, Mutability),
    Dynamic(Vec<Binder<ExistentialPredicate>>, Region, DynKind),
    #[custom_arm(FROM_TYPE::Coroutine(def_id, generics) => TO_TYPE::Coroutine(translate_item_ref(s, *def_id, generics)),)]
    Coroutine(ItemRef),
    Never,
    Tuple(Vec<Ty>),
    #[custom_arm(FROM_TYPE::Alias(alias_kind, alias_ty) => Alias::from(s, alias_kind, alias_ty),)]
    Alias(Alias),
    Param(ParamTy),
    Bound(DebruijnIndex, BoundTy),
    Placeholder(PlaceholderType),
    Infer(InferTy),
    #[custom_arm(FROM_TYPE::Error(..) => TO_TYPE::Error,)]
    Error,
    #[todo]
    Todo(String),
}

/// Reflects [`ty::Variance`]
#[derive(AdtInto)]
#[args(<S>, from: ty::Variance, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

/// Reflects [`ty::CanonicalUserTypeAnnotation`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct CanonicalUserTypeAnnotation {
    pub user_ty: CanonicalUserType,
    pub span: Span,
    pub inferred_ty: Ty,
}

/// Reflects [`ty::AdtKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Copy, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::AdtKind, state: S as _s)]
pub enum AdtKind {
    Struct,
    Union,
    Enum,
}

// This comes from MIR
// TODO: add the generics and the predicates
/// Reflects [`ty::AdtDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct AdtDef {
    pub did: DefId,
    pub adt_kind: AdtKind,
    pub variants: IndexVec<VariantIdx, VariantDef>,
    pub flags: AdtFlags,
    pub repr: ReprOptions,
}

sinto_todo!(rustc_middle::ty, AdtFlags);

/// Reflects [`ty::ReprOptions`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_abi::ReprOptions, state: S as s)]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    #[value({
        use crate::rustc_middle::ty::util::IntTypeExt;
        self.discr_type().to_ty(s.base().tcx).sinto(s)
    })]
    pub typ: Ty,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,
    pub field_shuffle_seed: u64,
}

sinto_todo!(rustc_abi, IntegerType);
sinto_todo!(rustc_abi, ReprFlags);
sinto_todo!(rustc_abi, Align);

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, AdtDef> for ty::AdtDef<'tcx> {
    fn sinto(&self, s: &S) -> AdtDef {
        let variants = self
            .variants()
            .iter_enumerated()
            .map(|(variant_idx, variant)| {
                let discr = if self.is_enum() {
                    self.discriminant_for_variant(s.base().tcx, variant_idx)
                } else {
                    // Structs and unions have a single variant.
                    assert_eq!(variant_idx.index(), 0);
                    ty::util::Discr {
                        val: 0,
                        ty: s.base().tcx.types.isize,
                    }
                };
                VariantDef::sfrom(s, variant, discr)
            })
            .collect();
        AdtDef {
            did: self.did().sinto(s),
            adt_kind: self.adt_kind().sinto(s),
            variants,
            flags: self.flags().sinto(s),
            repr: self.repr().sinto(s),
        }
    }
}

/// Reflects [`ty::adjustment::PointerCoercion`]
#[derive(AdtInto)]
#[args(<S>, from: ty::adjustment::PointerCoercion, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PointerCoercion {
    ReifyFnPointer,
    UnsafeFnPointer,
    ClosureFnPointer(Safety),
    MutToConstPointer,
    ArrayToPointer,
    DynStar,
    Unsize,
}

sinto_todo!(rustc_middle::ty, ScalarInt);

/// Reflects [`ty::FnSig`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::FnSig<'tcx>, state: S as s)]
pub struct TyFnSig {
    #[value(self.inputs().sinto(s))]
    pub inputs: Vec<Ty>,
    #[value(self.output().sinto(s))]
    pub output: Ty,
    pub c_variadic: bool,
    pub safety: Safety,
    pub abi: ExternAbi,
}

/// Reflects [`ty::PolyFnSig`]
pub type PolyFnSig = Binder<TyFnSig>;

/// Reflects [`ty::TraitRef`]
/// Contains the def_id and arguments passed to the trait. The first type argument is the `Self`
/// type. The `ImplExprs` are the _required_ predicate for this trait; currently they are always
/// empty because we consider all trait predicates as implied.
/// `self.in_trait` is always `None` because a trait can't be associated to another one.
pub type TraitRef = ItemRef;

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, TraitRef> for ty::TraitRef<'tcx> {
    fn sinto(&self, s: &S) -> TraitRef {
        translate_item_ref(s, self.def_id, self.args)
    }
}

/// Reflects [`ty::TraitPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::TraitPredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    #[map(*x == ty::PredicatePolarity::Positive)]
    #[from(polarity)]
    pub is_positive: bool,
}

/// Reflects [`ty::OutlivesPredicate`] as a named struct
/// instead of a tuple struct. This is because the script converting
/// JSONSchema types to OCaml doesn't support tuple structs, and this
/// is the only tuple struct in the whole AST.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OutlivesPredicate<T> {
    pub lhs: T,
    pub rhs: Region,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T, U> SInto<S, OutlivesPredicate<U>>
    for ty::OutlivesPredicate<'tcx, T>
where
    T: SInto<S, U>,
{
    fn sinto(&self, s: &S) -> OutlivesPredicate<U> where {
        OutlivesPredicate {
            lhs: self.0.sinto(s),
            rhs: self.1.sinto(s),
        }
    }
}

/// Reflects [`ty::RegionOutlivesPredicate`]
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
/// Reflects [`ty::TypeOutlivesPredicate`]
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;

/// Reflects [`ty::Term`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Ty(Ty),
    Const(ConstantExpr),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Term> for ty::Term<'tcx> {
    fn sinto(&self, s: &S) -> Term {
        use ty::TermKind;
        match self.unpack() {
            TermKind::Ty(ty) => Term::Ty(ty.sinto(s)),
            TermKind::Const(c) => Term::Const(c.sinto(s)),
        }
    }
}

/// Expresses a constraints over an associated type.
///
/// For instance:
/// ```text
/// fn f<T : Foo<S = String>>(...)
///              ^^^^^^^^^^
/// ```
/// (provided the trait `Foo` has an associated type `S`).
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProjectionPredicate {
    /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
    pub impl_expr: ImplExpr,
    /// The `Type` in `Ty: Trait<..., Type = U>`.
    pub assoc_item: AssocItem,
    /// The type `U` in `Ty: Trait<..., Type = U>`.
    pub ty: Ty,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderBinderState<'tcx>> SInto<S, ProjectionPredicate>
    for ty::ProjectionPredicate<'tcx>
{
    fn sinto(&self, s: &S) -> ProjectionPredicate {
        let tcx = s.base().tcx;
        let alias_ty = &self.projection_term.expect_ty(tcx);
        let poly_trait_ref = s.binder().rebind(alias_ty.trait_ref(tcx));
        let Term::Ty(ty) = self.term.sinto(s) else {
            unreachable!()
        };
        ProjectionPredicate {
            impl_expr: solve_trait(s, poly_trait_ref),
            assoc_item: tcx.associated_item(alias_ty.def_id).sinto(s),
            ty,
        }
    }
}

/// Reflects [`ty::ClauseKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderBinderState<'tcx>>, from: ty::ClauseKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    Projection(ProjectionPredicate),
    ConstArgHasType(ConstantExpr, Ty),
    WellFormed(Term),
    ConstEvaluatable(ConstantExpr),
    HostEffect(HostEffectPredicate),
}

sinto_todo!(rustc_middle::ty, HostEffectPredicate<'tcx>);

/// Reflects [`ty::Clause`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Clause {
    pub kind: Binder<ClauseKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for ty::Clause<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        let kind = self.kind().sinto(s);
        let id = kind.clone().map(PredicateKind::Clause).predicate_id();
        Clause { kind, id }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for ty::PolyTraitPredicate<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        let kind: Binder<_> = self.sinto(s);
        let kind: Binder<ClauseKind> = kind.map(ClauseKind::Trait);
        let id = kind.clone().map(PredicateKind::Clause).predicate_id();
        Clause { kind, id }
    }
}

/// Reflects [`ty::Predicate`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Predicate {
    pub kind: Binder<PredicateKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Predicate> for ty::Predicate<'tcx> {
    fn sinto(&self, s: &S) -> Predicate {
        let kind = self.kind().sinto(s);
        let id = kind.predicate_id();
        Predicate { kind, id }
    }
}

/// Reflects [`ty::BoundVariableKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundVariableKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BoundVariableKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

/// Reflects [`ty::Binder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Binder<T> {
    pub value: T,
    pub bound_vars: Vec<BoundVariableKind>,
}

impl<T> Binder<T> {
    pub fn as_ref(&self) -> Binder<&T> {
        Binder {
            value: &self.value,
            bound_vars: self.bound_vars.clone(),
        }
    }

    pub fn hax_skip_binder(self) -> T {
        self.value
    }

    pub fn hax_skip_binder_ref(&self) -> &T {
        &self.value
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder {
            value: f(self.value),
            bound_vars: self.bound_vars,
        }
    }

    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.value
    }

    pub fn rebind<U>(&self, value: U) -> Binder<U> {
        self.as_ref().map(|_| value)
    }
}

/// Reflects [`ty::GenericPredicates`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::GenericPredicates<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericPredicates {
    #[value(self.predicates.iter().map(|x| x.sinto(s)).collect())]
    pub predicates: Vec<(Clause, Span)>,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T1, T2> SInto<S, Binder<T2>> for ty::Binder<'tcx, T1>
where
    T1: SInto<StateWithBinder<'tcx>, T2>,
{
    fn sinto(&self, s: &S) -> Binder<T2> {
        let bound_vars = self.bound_vars().sinto(s);
        let value = {
            let under_binder_s = &State {
                base: s.base(),
                owner_id: s.owner_id(),
                binder: self.as_ref().map_bound(|_| ()),
                thir: (),
                mir: (),
            };
            self.as_ref().skip_binder().sinto(under_binder_s)
        };
        Binder { value, bound_vars }
    }
}

/// Reflects [`ty::SubtypePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::SubtypePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypePredicate {
    pub a_is_expected: bool,
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`ty::CoercePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::CoercePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CoercePredicate {
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`ty::AliasRelationDirection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::AliasRelationDirection, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasRelationDirection {
    Equate,
    Subtype,
}

/// Reflects [`ty::ClosureArgs`]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
#[derive_group(Serializers)]
pub struct ClosureArgs {
    pub item: ItemRef,
    /// The base kind of this closure. The kinds are ordered by inclusion: any `Fn` works as an
    /// `FnMut`, and any `FnMut` works as an `FnOnce`.
    pub kind: ClosureKind,
    /// The signature of the function that the closure implements, e.g. `fn(A, B, C) -> D`.
    pub fn_sig: PolyFnSig,
    /// The set of captured variables. Together they form the state of the closure.
    pub upvar_tys: Vec<Ty>,
}

#[cfg(feature = "rustc")]
impl ClosureArgs {
    // Manual implementation because we need the `def_id` of the closure.
    pub(crate) fn sfrom<'tcx, S>(
        s: &S,
        def_id: RDefId,
        from: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
    ) -> Self
    where
        S: UnderOwnerState<'tcx>,
    {
        let tcx = s.base().tcx;
        let sig = from.sig();
        let item = {
            // The closure has no generics of its own: it inherits its parent generics and could
            // have late-bound args but these are part of the signature.
            let parent_args = tcx.mk_args(from.parent_args());
            translate_item_ref(s, def_id, parent_args)
        };
        ClosureArgs {
            item,
            kind: from.kind().sinto(s),
            fn_sig: tcx
                .signature_unclosure(sig, rustc_hir::Safety::Safe)
                .sinto(s),
            upvar_tys: from.upvar_tys().sinto(s),
        }
    }
}

/// Reflects [`ty::ClosureKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ClosureKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

sinto_todo!(rustc_middle::ty, NormalizesTo<'tcx>);

/// Reflects [`ty::PredicateKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderBinderState<'tcx>>, from: ty::PredicateKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum PredicateKind {
    Clause(ClauseKind),
    DynCompatible(DefId),
    Subtype(SubtypePredicate),
    Coerce(CoercePredicate),
    ConstEquate(ConstantExpr, ConstantExpr),
    Ambiguous,
    AliasRelate(Term, Term, AliasRelationDirection),
    NormalizesTo(NormalizesTo),
}

/// Reflects [`ty::AssocItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::AssocItem, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AssocItem {
    pub def_id: DefId,
    /// This is `None` for RPTITs.
    #[value(self.opt_name().sinto(s))]
    pub name: Option<Symbol>,
    pub kind: AssocKind,
    #[value(get_container_for_assoc_item(s, self))]
    pub container: AssocItemContainer,
    /// Whether this item has a value (e.g. this is `false` for trait methods without default
    /// implementations).
    #[value(self.defaultness(s.base().tcx).has_value())]
    pub has_value: bool,
}

/// Reflects [`ty::AssocKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::AssocKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocKind {
    Const { name: Symbol },
    Fn { name: Symbol, has_self: bool },
    Type { data: AssocTypeData },
}

/// Reflects [`ty::AssocTypeData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::AssocTypeData, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocTypeData {
    Normal(Symbol),
    Rpitit(ImplTraitInTraitData),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocItemContainer {
    TraitContainer {
        trait_ref: TraitRef,
    },
    TraitImplContainer {
        /// Reference to the def_id of the impl block.
        impl_: ItemRef,
        /// The trait ref implemented by the impl block.
        implemented_trait_ref: TraitRef,
        /// The def_id of the associated item (in the trait declaration) that is being implemented.
        implemented_trait_item: DefId,
        /// Whether the corresponding trait item had a default (and therefore this one overrides
        /// it).
        overrides_default: bool,
    },
    InherentImplContainer {
        impl_id: DefId,
    },
}

#[cfg(feature = "rustc")]
fn get_container_for_assoc_item<'tcx, S: BaseState<'tcx>>(
    s: &S,
    item: &ty::AssocItem,
) -> AssocItemContainer {
    let tcx = s.base().tcx;
    // We want to solve traits in the context of this item.
    let state_with_id = &with_owner_id(s.base(), (), (), item.def_id);
    let container_id = item.container_id(tcx);
    match item.container {
        ty::AssocItemContainer::Trait => {
            let trait_ref = ty::TraitRef::identity(tcx, container_id).sinto(state_with_id);
            AssocItemContainer::TraitContainer { trait_ref }
        }
        ty::AssocItemContainer::Impl => {
            if let Some(implemented_trait_item) = item.trait_item_def_id {
                let impl_generics = ty::GenericArgs::identity_for_item(tcx, container_id);
                let item = translate_item_ref(state_with_id, container_id, impl_generics);
                let implemented_trait_ref = tcx
                    .impl_trait_ref(container_id)
                    .unwrap()
                    .instantiate_identity();
                AssocItemContainer::TraitImplContainer {
                    impl_: item,
                    implemented_trait_ref: implemented_trait_ref.sinto(state_with_id),
                    implemented_trait_item: implemented_trait_item.sinto(s),
                    overrides_default: tcx.defaultness(implemented_trait_item).has_value(),
                }
            } else {
                AssocItemContainer::InherentImplContainer {
                    impl_id: container_id.sinto(s),
                }
            }
        }
    }
}

/// Reflects [`ty::ImplTraitInTraitData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::ImplTraitInTraitData, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplTraitInTraitData {
    Trait {
        fn_def_id: DefId,
        opaque_def_id: DefId,
    },
    Impl {
        fn_def_id: DefId,
    },
}
