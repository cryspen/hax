module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

let slice_length (#a: Type) (s: t_Slice a): res: usize {res == sz (FStar.List.Tot.length s)} = sz (FStar.List.Tot.length s)
let slice_split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize {mid <=. length s}): t_Slice v_T & t_Slice v_T =
  list_slice s 0 (v mid), list_slice s (v mid) (FStar.List.Tot.length s)
let slice_contains (#a: eqtype) (s: t_Slice a) (v: a): bool = FStar.List.Tot.mem v s
let slice_index (#t: Type) (s: t_Slice t) (i: usize {i <. length s}): t = FStar.List.Tot.index s (v i)
let slice_slice (#v_T: Type0) (s: t_Slice v_T) (start: usize {start <=. length s}) (end_: usize {start <=. end_ /\ end_ <=. length s}): t_Slice v_T =
  list_slice s (v start) (v end_)
val array_map (#t: Type) (#u: Type) (l: usize) (#ft: Type)
  (s: t_Array t l) (f: t -> u): res: t_Array u l {forall i. FStar.List.Tot.index res i == f (FStar.List.Tot.index s i)}
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
let array_slice (#t: Type) (l: usize) (s: t_Array t l) = slice_slice s
val array_from_fn (#t: Type) (len: usize) (#ft: Type) (f: (x: usize {x <. len}) -> t):
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. FStar.List.Tot.index a i == f (sz i)))
let array_index (#t: Type) (l: usize) (s: t_Array t l) (i: usize {i <. length s}): t = FStar.List.Tot.index s (v i)
