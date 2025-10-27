module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

let length (#a: Type) (s: t_Slice a): res: usize {res == sz (Seq.length s)} = sz (Seq.length s)
let split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize {mid <=. length s}): t_Slice v_T & t_Slice v_T = 
  Seq.slice s 0 (v mid), Seq.slice s (v mid) (Seq.length s)
let slice_index (#t: Type) (s: t_Slice t) (i: usize {i <. length s}): t = Seq.index s (v i)
let array_map (#t: Type) (#u: Type) (l: usize) (#v_F: Type) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F t)
  (#_: unit{i0.Core_models.Ops.Function.f_Output == u})
  (s: t_Array t l) (f: v_F): t_Array u l =
  Rust_primitives.Arrays.map_array s (Core_models.Ops.Function.f_call_once f)
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
val array_from_fn (#t: Type) (len: usize) (#v_F: Type) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F usize)
  (#_: unit{i0.Core_models.Ops.Function.f_Output == t}) (f: v_F): 
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. Seq.index a i == Core_models.Ops.Function.f_call_once f (sz i)))

