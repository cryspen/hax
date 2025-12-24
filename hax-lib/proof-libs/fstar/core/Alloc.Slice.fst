module Alloc.Slice
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let impl__to_vec (#v_T: Type0) (s: t_Slice v_T) : Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global =
  Alloc.Vec.Vec (Rust_primitives.Sequence.seq_from_slice #v_T s)
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global

let impl__into_vec (#v_T #v_A: Type0) (s: t_Slice v_T) : Alloc.Vec.t_Vec v_T v_A =
  Alloc.Vec.Vec (Rust_primitives.Sequence.seq_from_slice #v_T s)
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
  <:
  Alloc.Vec.t_Vec v_T v_A

assume
val impl__sort_by':
    #v_T: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F (v_T & v_T) |} ->
    s: t_Slice v_T ->
    compare: v_F
  -> t_Slice v_T

unfold
let impl__sort_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F (v_T & v_T))
     = impl__sort_by' #v_T #v_F #i0
