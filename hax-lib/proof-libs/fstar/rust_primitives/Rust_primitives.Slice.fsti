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
val array_map (#t: Type) (#u: Type) (l: usize) (#ft: Type)
  (s: t_Array t l) (f: t -> u): res: t_Array u l {forall i. Seq.index res i == f (Seq.index s i)}
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
let array_slice (#t: Type) (l: usize) (s: t_Array t l) = slice_slice s
val array_from_fn (#t: Type) (len: usize) (#ft: Type) (f: (x: usize {x <. len}) -> t): 
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. Seq.index a i == f (sz i)))
let array_index (#t: Type) (l: usize) (s: t_Array t l) (i: usize {i <. length s}): t = Seq.index s (v i)
// Kept in this module (rather than written as an array literal in the model) so
// that `Core_models` does not reach `Rust_primitives.Hax.array_of_list`, which
// would make hax's bundle and `Rust_primitives.Hax` mutually dependent.
let array_pair (#t: Type) (x y: t): t_Array t (mk_usize 2) =
  Rust_primitives.Arrays.createi (mk_usize 2) (fun i -> if i =. mk_usize 0 then x else y)
let array_from_ref (#t: Type) (x: t): t_Array t (mk_usize 1) = Seq.create 1 x
