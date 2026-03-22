module Rust_primitives.Sequence

open Rust_primitives.Integers

type t_Seq t = Rust_primitives.Arrays.t_Slice t

let seq_empty #t () : t_Seq t = []

let seq_from_slice #t (s: Rust_primitives.Arrays.t_Slice t) : t_Seq t = s

let seq_from_array #t n (s: Rust_primitives.Arrays.t_Array t n) : t_Seq t = s

let seq_to_slice #t (s: t_Seq t) : Rust_primitives.Arrays.t_Slice t = s

let seq_len #t (s: t_Seq t): usize = mk_usize (FStar.List.Tot.length s)

let seq_slice #t (s: t_Seq t) (b: usize) (e: usize{e >=. b && e <=. seq_len s}): (r:t_Seq t{FStar.List.Tot.length r == v e - v b}) =
  Rust_primitives.Arrays.list_slice s (v b) (v e)

let seq_index #t (s: t_Seq t) (i: usize{i <. seq_len s}): t = FStar.List.Tot.index s (v i)

let seq_last #t (s: t_Seq t{seq_len s >. mk_usize 0}): t = FStar.List.Tot.index s ((FStar.List.Tot.length s) - 1)

let seq_first #t (s: t_Seq t{seq_len s >. mk_usize 0}): t = FStar.List.Tot.index s 0

#push-options "--fuel 1"
let seq_concat #t (s1: t_Seq t) (s2: t_Seq t {(FStar.List.Tot.length s1) + (FStar.List.Tot.length s2) <= max_usize}): (r:t_Seq t{FStar.List.Tot.length r == FStar.List.Tot.length s1 + FStar.List.Tot.length s2}) =
  FStar.List.Tot.Properties.append_length s1 s2;
  FStar.List.Tot.append s1 s2
#pop-options

let seq_one #t (x: t): (s:t_Seq t{FStar.List.Tot.length s == 1}) = [x]

let seq_create #t (x: t) (n: usize): t_Seq t = Rust_primitives.Arrays.list_create (v n) x
