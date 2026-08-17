module Core_models.Iter.Sources.Repeat_with
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::RepeatWith`]
type t_RepeatWith (v_F: Type0) = { f_repeater:v_F }

/// See [`std::iter::repeat_with`]
let repeat_with
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
      (repeater: v_F)
    : t_RepeatWith v_F = { f_repeater = repeater } <: t_RepeatWith v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_RepeatWith v_F) =
  {
    f_Item = v_A;
    f_next_pre = (fun (self: t_RepeatWith v_F) -> true);
    f_next_post
    =
    (fun (self: t_RepeatWith v_F) (out1: (t_RepeatWith v_F & Core_models.Option.t_Option v_A)) ->
        true);
    f_next
    =
    fun (self: t_RepeatWith v_F) ->
      let (tmp0: v_F), (out: v_A) =
        Core_models.Ops.Function.f_call_mut #v_F
          #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          self.f_repeater
          (() <: Prims.unit)
      in
      let self:t_RepeatWith v_F = { self with f_repeater = tmp0 } <: t_RepeatWith v_F in
      let hax_temp_output:Core_models.Option.t_Option v_A =
        Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_A
      in
      self, hax_temp_output <: (t_RepeatWith v_F & Core_models.Option.t_Option v_A)
  }
