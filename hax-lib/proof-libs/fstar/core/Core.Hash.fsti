module Core.Hash


open Rust_primitives.Arrays
open Rust_primitives.Integers

class t_Hasher (v_Self: Type0) = {
  hax_dummy_hasher_field: Prims.unit;
}

class t_Hash (v_Self: Type0) = {
  f_hash_pre:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      v_Self ->
      v_H
    -> Type0;
  f_hash_post:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      v_Self ->
      v_H ->
      v_H
    -> Type0;
  f_hash:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      x0: v_Self ->
      x1: v_H
    -> Prims.Pure v_H
        (f_hash_pre #v_H #i1 x0 x1)
        (fun result ->
            f_hash_post #v_H
              #i1
              x0
              x1
              result);
  (* f_hash_slice_pre:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      t_Slice v_Self ->
      v_H
    -> Type0;
  f_hash_slice_post:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      t_Slice v_Self ->
      v_H ->
      v_H
    -> Type0;
  f_hash_slice:
      #v_H: Type0 ->
      {| i1: t_Hasher v_H |} ->
      x0: t_Slice v_Self ->
      x1: v_H
    -> Prims.Pure v_H
        (f_hash_slice_pre #v_H #i1 x0 x1)
        (fun result ->
            f_hash_slice_post #v_H
              #i1
              x0
              x1
              result) *)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val hash_vec (t: Type0): t_Hash (Alloc.Vec.t_Vec t Alloc.Alloc.t_Global)
