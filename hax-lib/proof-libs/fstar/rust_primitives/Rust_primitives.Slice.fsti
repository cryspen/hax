module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

let slice_length (#a: Type) (s: t_Slice a): res: usize {res == sz (Seq.length s)} = sz (Seq.length s)
let slice_split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize {mid <=. length s}): t_Slice v_T & t_Slice v_T = 
  Seq.slice s 0 (v mid), Seq.slice s (v mid) (Seq.length s)
let slice_contains (#a: eqtype) (s: t_Slice a) (v: a): bool = Seq.mem v s
let slice_index (#t: Type) (s: t_Slice t) (i: usize {i <. length s}): t = Seq.index s (v i)
let slice_slice (#v_T: Type0) (s: t_Slice v_T) (start: usize {start <=. length s}) (end_: usize {start <=. end_ /\ end_ <=. length s}): t_Slice v_T =
  Seq.slice s (v start) (v end_)
let slice_clone_from_slice (#v_T: Type0) (s: t_Slice v_T) (src: t_Slice v_T {slice_length src == slice_length s}): t_Slice v_T = src
val array_map 
      (#v_T #v_U: Type0)
      (v_N: usize)
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
      (#_: unit{i0._super_i0._super_i0.Core_models.Ops.Function.f_Output == v_U})
      (s: t_Array v_T v_N)
      (f: v_F)
      : res: t_Array v_U v_N {forall i. Seq.index res i == Core_models.Ops.Function.f_call f (Seq.index s i)}
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
let array_slice (#t: Type) (l: usize) (s: t_Array t l) = slice_slice s
val array_from_fn 
      (#v_T: Type0)
      (v_N: usize)
      (#v_F: Type0)
      (f: (i: usize {i <. v_N}) -> v_T): 
  Pure (t_Array v_T v_N) (requires True) (ensures (fun a -> forall i. Seq.index a i == f (sz i)))
let array_index (#t: Type) (l: usize) (s: t_Array t l) (i: usize {i <. length s}): t = Seq.index s (v i)
