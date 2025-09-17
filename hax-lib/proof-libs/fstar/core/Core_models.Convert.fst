module Core_models.Convert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Into (v_Self: Type0) (v_T: Type0) = {
  f_into_pre:v_Self -> Type0;
  f_into_post:v_Self -> v_T -> Type0;
  f_into:x0: v_Self -> Prims.Pure v_T (f_into_pre x0) (fun result -> f_into_post x0 result)
}

class t_From (v_Self: Type0) (v_T: Type0) = {
  f_from_pre:v_T -> Type0;
  f_from_post:v_T -> v_Self -> Type0;
  f_from:x0: v_T -> Prims.Pure v_Self (f_from_pre x0) (fun result -> f_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_Into v_T v_U =
  {
    f_into_pre = (fun (self: v_T) -> true);
    f_into_post = (fun (self: v_T) (out: v_U) -> true);
    f_into = fun (self: v_T) -> f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }

type t_Infallible = | Infallible : t_Infallible

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : t_From v_T v_T =
  {
    f_from_pre = (fun (x: v_T) -> true);
    f_from_post = (fun (x: v_T) (out: v_T) -> true);
    f_from = fun (x: v_T) -> x
  }

class t_AsRef (v_Self: Type0) (v_T: Type0) = {
  f_as_ref_pre:v_Self -> Type0;
  f_as_ref_post:v_Self -> v_T -> Type0;
  f_as_ref:x0: v_Self -> Prims.Pure v_T (f_as_ref_pre x0) (fun result -> f_as_ref_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : t_AsRef v_T v_T =
  {
    f_as_ref_pre = (fun (self: v_T) -> true);
    f_as_ref_post = (fun (self: v_T) (out: v_T) -> true);
    f_as_ref = fun (self: v_T) -> self
  }

class t_TryInto (v_Self: Type0) (v_T: Type0) = {
  f_Error:Type0;
  f_try_into_pre:v_Self -> Type0;
  f_try_into_post:v_Self -> Core_models.Result.t_Result v_T f_Error -> Type0;
  f_try_into:x0: v_Self
    -> Prims.Pure (Core_models.Result.t_Result v_T f_Error)
        (f_try_into_pre x0)
        (fun result -> f_try_into_post x0 result)
}

class t_TryFrom (v_Self: Type0) (v_T: Type0) = {
  f_Error:Type0;
  f_try_from_pre:v_T -> Type0;
  f_try_from_post:v_T -> Core_models.Result.t_Result v_Self f_Error -> Type0;
  f_try_from:x0: v_T
    -> Prims.Pure (Core_models.Result.t_Result v_Self f_Error)
        (f_try_from_pre x0)
        (fun result -> f_try_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_TryFrom v_U v_T =
  {
    f_Error = t_Infallible;
    f_try_from_pre = (fun (x: v_T) -> true);
    f_try_from_post = (fun (x: v_T) (out: Core_models.Result.t_Result v_U t_Infallible) -> true);
    f_try_from
    =
    fun (x: v_T) ->
      Core_models.Result.Result_Ok (f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve x)
      <:
      Core_models.Result.t_Result v_U t_Infallible
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_TryFrom v_U v_T)
    : t_TryInto v_T v_U =
  {
    f_Error = i0.f_Error;
    f_try_into_pre = (fun (self: v_T) -> true);
    f_try_into_post = (fun (self: v_T) (out: Core_models.Result.t_Result v_U i0.f_Error) -> true);
    f_try_into = fun (self: v_T) -> f_try_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }
