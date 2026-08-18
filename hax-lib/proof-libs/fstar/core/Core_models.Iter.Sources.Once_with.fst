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
assume
val impl':
    #v_A: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_FnOnce v_F Prims.unit |} ->
    #_: unit{i0.Core_models.Ops.Function.f_Output == v_A}
  -> Core_models.Iter.Traits.Iterator.t_Iterator (t_OnceWith v_F)

unfold
let impl
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_A})
     = impl' #v_A #v_F #i0 #_
