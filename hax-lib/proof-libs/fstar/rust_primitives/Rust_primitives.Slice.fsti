module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

let length (#a: Type) (s: t_Slice a): res: usize {res == sz (Seq.length s)} = sz (Seq.length s)
let split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize {mid <=. length s}): t_Slice v_T & t_Slice v_T = 
  Seq.slice s 0 (v mid), Seq.slice s (v mid) (Seq.length s)
let slice_index (#t: Type) (s: t_Slice t) (i: usize {i <. length s}): t = Seq.index s (v i)
val array_map (#t: Type) (#u: Type) (l: usize)
  (s: t_Array t l) (f: t -> u): res: t_Array u l {forall i. Seq.index res i == f (Seq.index s i)}
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
val array_from_fn (#t: Type) (len: usize) (f: (x: usize {x <. len}) -> t): 
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. Seq.index a i == f (sz i)))
let array_from_closure = array_from_fn
