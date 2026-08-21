module Core_models.Iter.Sources.Successors
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Successors`]
type t_Successors (v_T: Type0) (v_F: Type0) = {
  f_next:Rust_primitives.Sequence.t_Seq v_T;
  f_succ:v_F
}

/// See [`std::iter::successors`]
let successors
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
      (first: Core_models.Option.t_Option v_T)
      (succ: v_F)
    : t_Successors v_T v_F =
  let next:Rust_primitives.Sequence.t_Seq v_T =
    match first <: Core_models.Option.t_Option v_T with
    | Core_models.Option.Option_Some v -> Rust_primitives.Sequence.seq_one #v_T v
    | Core_models.Option.Option_None  -> Rust_primitives.Sequence.seq_empty #v_T ()
  in
  { f_next = next; f_succ = succ } <: t_Successors v_T v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': #v_T: Type0 -> #v_F: Type0 -> {| i0: Core_models.Ops.Function.t_Fn v_F v_T |}
  -> Core_models.Iter.Traits.Iterator.t_Iterator (t_Successors v_T v_F)

unfold
let impl
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl' #v_T #v_F #i0
