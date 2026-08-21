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
assume
val impl': #v_A: Type0 -> #v_F: Type0 -> {| i0: Core_models.Ops.Function.t_FnMut v_F Prims.unit |}
  -> Core_models.Iter.Traits.Iterator.t_Iterator (t_RepeatWith v_F)

unfold
let impl
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
     = impl' #v_A #v_F #i0
