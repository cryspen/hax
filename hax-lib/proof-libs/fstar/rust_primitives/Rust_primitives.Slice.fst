module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

#set-options "--fuel 1 --ifuel 0 --z3rlimit 30"

let array_map (#t: Type) (#u: Type) (l: usize) (#ft: Type)
  (s: t_Array t l) (f: t -> u): res: t_Array u l {forall i. FStar.List.Tot.index res i == f (FStar.List.Tot.index s i)}
  = admit (); // TODO: prove forall postcondition
    list_init (v l) (fun i -> f (FStar.List.Tot.index s i))

let array_from_fn (#t: Type) (len: usize) (#ft: Type) (f: (x: usize {x <. len}) -> t):
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. FStar.List.Tot.index a i == f (sz i)))
  = admit (); // TODO: prove forall postcondition
    list_init (v len) (fun i -> f (sz i))
