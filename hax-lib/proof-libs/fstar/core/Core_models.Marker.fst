module Core_models.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::marker::Copy`]
class t_Copy (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Clone.t_Clone v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Copy v_Self|} -> i._super_i0

/// See [`std::marker::Send`]
class t_Send (v_Self: Type0) = { __marker_trait_t_Send:Prims.unit }

/// See [`std::marker::Sync`]
class t_Sync (v_Self: Type0) = { __marker_trait_t_Sync:Prims.unit }

/// See [`std::marker::Sized`]
class t_Sized (v_Self: Type0) = { __marker_trait_t_Sized:Prims.unit }

/// See [`std::marker::StructuralPartialEq`]
class t_StructuralPartialEq (v_Self: Type0) = { __marker_trait_t_StructuralPartialEq:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Send v_T = { __marker_trait_t_Send = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_Sync v_T = { __marker_trait_t_Sync = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_Sized v_T = { __marker_trait_t_Sized = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
    : t_Copy v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T

/// See [`std::marker::MetaSized`]
class t_MetaSized (v_Self: Type0) = { __marker_trait_t_MetaSized:Prims.unit }

/// See [`std::marker::PointeeSized`]
class t_PointeeSized (v_Self: Type0) = { __marker_trait_t_PointeeSized:Prims.unit }

/// See [`std::marker::Unsize`]
class t_Unsize (v_Self: Type0) (v_T: Type0) = { __marker_trait_t_Unsize:Prims.unit }

/// See [`std::marker::Freeze`]
class t_Freeze (v_Self: Type0) = { __marker_trait_t_Freeze:Prims.unit }

/// See [`std::marker::Unpin`]
class t_Unpin (v_Self: Type0) = { __marker_trait_t_Unpin:Prims.unit }

/// See [`std::marker::Destruct`]
class t_Destruct (v_Self: Type0) = { __marker_trait_t_Destruct:Prims.unit }

/// See [`std::marker::Tuple`]
class t_Tuple (v_Self: Type0) = { __marker_trait_t_Tuple:Prims.unit }

/// See [`std::marker::ConstParamTy_`]
class t_ConstParamTy_ (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_StructuralPartialEq v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_ConstParamTy_ v_Self|} -> i._super_i0

/// See [`std::marker::FnPtr`]
class t_FnPtr (v_Self: Type0) = { [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Copy v_Self }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_FnPtr v_Self|} -> i._super_i0

/// See [`std::marker::DiscriminantKind`]
class t_DiscriminantKind (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Discriminant:Type0
}

/// See [`std::marker::PhantomPinned`]
type t_PhantomPinned = | PhantomPinned : t_PhantomPinned

/// See [`std::marker::Variance`]. std seals this trait behind an associated
/// `const VALUE: Self`; the model uses the `Default` supertrait std also
/// requires, which is what [`variance`] is documented to be equivalent to.
class t_Variance (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Default.t_Default v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Variance v_Self|} -> i._super_i0

/// See [`std::marker::variance`]
let variance
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Variance v_T)
      (_: Prims.unit)
    : v_T = Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::marker::PhantomCovariant`] (and similar for the other
/// variance markers)
type t_PhantomCovariant (v_T: Type0) =
  | PhantomCovariant : t_PhantomData v_T -> t_PhantomCovariant v_T

/// See [`std::marker::PhantomCovariant::new`] (and similar for
/// the other variance markers)
let impl_4__new (#v_T: Type0) (_: Prims.unit) : t_PhantomCovariant v_T =
  PhantomCovariant (PhantomData <: t_PhantomData v_T) <: t_PhantomCovariant v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomCovariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_4__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : t_Variance (t_PhantomCovariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomCovariant`] (and similar for the other
/// variance markers)
type t_PhantomContravariant (v_T: Type0) =
  | PhantomContravariant : t_PhantomData v_T -> t_PhantomContravariant v_T

/// See [`std::marker::PhantomCovariant::new`] (and similar for
/// the other variance markers)
let impl_6__new (#v_T: Type0) (_: Prims.unit) : t_PhantomContravariant v_T =
  PhantomContravariant (PhantomData <: t_PhantomData v_T) <: t_PhantomContravariant v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomContravariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_6__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_T: Type0) : t_Variance (t_PhantomContravariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomCovariant`] (and similar for the other
/// variance markers)
type t_PhantomInvariant (v_T: Type0) =
  | PhantomInvariant : t_PhantomData v_T -> t_PhantomInvariant v_T

/// See [`std::marker::PhantomCovariant::new`] (and similar for
/// the other variance markers)
let impl_8__new (#v_T: Type0) (_: Prims.unit) : t_PhantomInvariant v_T =
  PhantomInvariant (PhantomData <: t_PhantomData v_T) <: t_PhantomInvariant v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomInvariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_8__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (#v_T: Type0) : t_Variance (t_PhantomInvariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomCovariantLifetime`] (and similar for
/// the other variance-lifetime markers)
type t_PhantomCovariantLifetime =
  | PhantomCovariantLifetime : t_PhantomCovariant Prims.unit -> t_PhantomCovariantLifetime

/// See [`std::marker::PhantomCovariantLifetime::new`] (and
/// similar for the other variance-lifetime markers)
let impl_13__new (_: Prims.unit) : t_PhantomCovariantLifetime =
  PhantomCovariantLifetime (impl_4__new #Prims.unit ()) <: t_PhantomCovariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core_models.Default.t_Default t_PhantomCovariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_13__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: t_Variance t_PhantomCovariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomCovariantLifetime`] (and similar for
/// the other variance-lifetime markers)
type t_PhantomContravariantLifetime =
  | PhantomContravariantLifetime : t_PhantomContravariant Prims.unit
    -> t_PhantomContravariantLifetime

/// See [`std::marker::PhantomCovariantLifetime::new`] (and
/// similar for the other variance-lifetime markers)
let impl_15__new (_: Prims.unit) : t_PhantomContravariantLifetime =
  PhantomContravariantLifetime (impl_6__new #Prims.unit ()) <: t_PhantomContravariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core_models.Default.t_Default t_PhantomContravariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_15__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: t_Variance t_PhantomContravariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomCovariantLifetime`] (and similar for
/// the other variance-lifetime markers)
type t_PhantomInvariantLifetime =
  | PhantomInvariantLifetime : t_PhantomInvariant Prims.unit -> t_PhantomInvariantLifetime

/// See [`std::marker::PhantomCovariantLifetime::new`] (and
/// similar for the other variance-lifetime markers)
let impl_17__new (_: Prims.unit) : t_PhantomInvariantLifetime =
  PhantomInvariantLifetime (impl_8__new #Prims.unit ()) <: t_PhantomInvariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core_models.Default.t_Default t_PhantomInvariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_17__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: t_Variance t_PhantomInvariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }
