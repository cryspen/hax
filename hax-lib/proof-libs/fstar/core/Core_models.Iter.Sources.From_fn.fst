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
assume
val impl': #v_T: Type0 -> #v_F: Type0 -> {| i0: Core_models.Ops.Function.t_FnMut v_F Prims.unit |}
  -> Core_models.Iter.Traits.Iterator.t_Iterator (t_FromFn v_F)

unfold
let impl
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F Prims.unit)
     = impl' #v_T #v_F #i0
