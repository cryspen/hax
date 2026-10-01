module Core_models.Marker.Variance
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::marker::Variance`]. Uses `Default` rather than a `VALUE` const.
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

/// See [`std::marker::PhantomCovariant`]
type t_PhantomCovariant (v_T: Type0) =
  | PhantomCovariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomCovariant v_T

/// See [`std::marker::PhantomContravariant`]
type t_PhantomContravariant (v_T: Type0) =
  | PhantomContravariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomContravariant v_T

/// See [`std::marker::PhantomInvariant`]
type t_PhantomInvariant (v_T: Type0) =
  | PhantomInvariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomInvariant v_T

/// See [`std::marker::PhantomCovariantLifetime`]
type t_PhantomCovariantLifetime =
  | PhantomCovariantLifetime : t_PhantomCovariant Prims.unit -> t_PhantomCovariantLifetime

/// See [`std::marker::PhantomContravariantLifetime`]
type t_PhantomContravariantLifetime =
  | PhantomContravariantLifetime : t_PhantomContravariant Prims.unit
    -> t_PhantomContravariantLifetime

/// See [`std::marker::PhantomInvariantLifetime`]
type t_PhantomInvariantLifetime =
  | PhantomInvariantLifetime : t_PhantomInvariant Prims.unit -> t_PhantomInvariantLifetime

/// See [`std::marker::PhantomCovariant::new`]
let impl_39__new (#v_T: Type0) (_: Prims.unit) : t_PhantomCovariant v_T =
  PhantomCovariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomCovariant v_T

/// See [`std::marker::PhantomCovariantLifetime::new`]
let impl__new (_: Prims.unit) : t_PhantomCovariantLifetime =
  PhantomCovariantLifetime (impl_39__new #Prims.unit ()) <: t_PhantomCovariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Default.t_Default t_PhantomCovariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_Variance t_PhantomCovariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomCovariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_39__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41 (#v_T: Type0) : t_Variance (t_PhantomCovariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomContravariant::new`]
let impl_51__new (#v_T: Type0) (_: Prims.unit) : t_PhantomContravariant v_T =
  PhantomContravariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomContravariant v_T

/// See [`std::marker::PhantomContravariantLifetime::new`]
let impl_4__new (_: Prims.unit) : t_PhantomContravariantLifetime =
  PhantomContravariantLifetime (impl_51__new #Prims.unit ()) <: t_PhantomContravariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core_models.Default.t_Default t_PhantomContravariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_4__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_Variance t_PhantomContravariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomContravariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_51__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53 (#v_T: Type0) : t_Variance (t_PhantomContravariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::PhantomInvariant::new`]
let impl_63__new (#v_T: Type0) (_: Prims.unit) : t_PhantomInvariant v_T =
  PhantomInvariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomInvariant v_T

/// See [`std::marker::PhantomInvariantLifetime::new`]
let impl_8__new (_: Prims.unit) : t_PhantomInvariantLifetime =
  PhantomInvariantLifetime (impl_63__new #Prims.unit ()) <: t_PhantomInvariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core_models.Default.t_Default t_PhantomInvariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_8__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_Variance t_PhantomInvariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomInvariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariant v_T) -> true);
    f_default = fun (_: Prims.unit) -> impl_63__new #v_T ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65 (#v_T: Type0) : t_Variance (t_PhantomInvariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }
