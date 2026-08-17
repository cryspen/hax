module Core_models.Iter.Sources.From_fn
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::FromFn`]
type t_FromFn (v_F: Type0) = | FromFn : v_F -> t_FromFn v_F

/// See [`std::iter::from_fn`]
let from_fn
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
      (f: v_F)
    : t_FromFn v_F = FromFn f <: t_FromFn v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_FromFn v_F) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_FromFn v_F) -> true);
    f_next_post
    =
    (fun (self: t_FromFn v_F) (out1: (t_FromFn v_F & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_FromFn v_F) ->
      let (tmp0: v_F), (out: Core_models.Option.t_Option v_T) =
        Core_models.Ops.Function.f_call_mut #v_F
          #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          self._0
          (() <: Prims.unit)
      in
      let self:t_FromFn v_F = { self with _0 = tmp0 } <: t_FromFn v_F in
      let hax_temp_output:Core_models.Option.t_Option v_T = out in
      self, hax_temp_output <: (t_FromFn v_F & Core_models.Option.t_Option v_T)
  }
