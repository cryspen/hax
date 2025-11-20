module Alloc.Collections.Binary_heap
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val t_BinaryHeap (v_T v_U: Type0) : eqtype

val impl_9__new: #v_T: Type0 -> #v_U: Type0 -> Prims.unit
  -> Prims.Pure (t_BinaryHeap v_T v_U) Prims.l_True (fun _ -> Prims.l_True)

val impl_9__push (#v_T #v_U: Type0) (self: t_BinaryHeap v_T v_U) (v: v_T)
    : Prims.Pure (t_BinaryHeap v_T v_U) Prims.l_True (fun _ -> Prims.l_True)

val impl_9__pop (#v_T #v_U: Type0) (self: t_BinaryHeap v_T v_U)
    : Prims.Pure (t_BinaryHeap v_T v_U & Core_models.Option.t_Option v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)
