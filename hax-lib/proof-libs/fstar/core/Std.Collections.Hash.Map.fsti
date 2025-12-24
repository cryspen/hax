module Std.Collections.Hash.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

val t_HashMap (v_K v_V v_S: Type0) : eqtype

val impl__new: #v_K: Type0 -> #v_V: Type0 -> Prims.unit
  -> Prims.Pure (t_HashMap v_K v_V Std.Hash.Random.t_RandomState)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__get (#v_K #v_V #v_S #v_Y: Type0) (m: t_HashMap v_K v_V v_S) (k: v_K)
    : Prims.Pure (Core_models.Option.t_Option v_V) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__insert (#v_K #v_V #v_S: Type0) (m: t_HashMap v_K v_V v_S) (k: v_K) (v: v_V)
    : Prims.Pure (t_HashMap v_K v_V v_S & Core_models.Option.t_Option v_V)
      Prims.l_True
      (fun _ -> Prims.l_True)
