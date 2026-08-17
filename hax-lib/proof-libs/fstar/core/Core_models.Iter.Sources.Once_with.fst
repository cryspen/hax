module Core_models.Iter.Sources.Once_with
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::OnceWith`]
type t_OnceWith (v_F: Type0) = | OnceWith : Rust_primitives.Sequence.t_Seq v_F -> t_OnceWith v_F

/// See [`std::iter::once_with`]
let once_with
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_A})
      (make: v_F)
    : t_OnceWith v_F = OnceWith (Rust_primitives.Sequence.seq_one #v_F make) <: t_OnceWith v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_A})
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_OnceWith v_F) =
  {
    f_Item = v_A;
    f_next_pre = (fun (self: t_OnceWith v_F) -> true);
    f_next_post
    =
    (fun (self: t_OnceWith v_F) (out1: (t_OnceWith v_F & Core_models.Option.t_Option v_A)) -> true);
    f_next
    =
    fun (self: t_OnceWith v_F) ->
      let (self: t_OnceWith v_F), (hax_temp_output: Core_models.Option.t_Option v_A) =
        if (Rust_primitives.Sequence.seq_len #v_F self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_A)
          <:
          (t_OnceWith v_F & Core_models.Option.t_Option v_A)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_F), (out: v_F) =
            Rust_primitives.Sequence.seq_remove #v_F self._0 (mk_usize 0)
          in
          let self:t_OnceWith v_F = { self with _0 = tmp0 } <: t_OnceWith v_F in
          self,
          (Core_models.Option.Option_Some
            (Core_models.Ops.Function.f_call_once #v_F
                #Prims.unit
                #FStar.Tactics.Typeclasses.solve
                out
                (() <: Prims.unit))
            <:
            Core_models.Option.t_Option v_A)
          <:
          (t_OnceWith v_F & Core_models.Option.t_Option v_A)
      in
      self, hax_temp_output <: (t_OnceWith v_F & Core_models.Option.t_Option v_A)
  }
