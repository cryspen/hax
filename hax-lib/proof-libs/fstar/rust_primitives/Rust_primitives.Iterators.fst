module Rust_primitives.Iterators

open Rust_primitives
open Core_models.Ops.Range
open FStar.Mul

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* These functions are implemented with recursive helper + admit for postconditions.
   The computation itself is correct; only the invariant proofs are admitted. *)

let rec foldi_range_impl (#n:inttype) (#acc_t:Type)
  (start end_: int_t n)
  (acc: acc_t)
  (f: acc_t -> int_t n -> acc_t)
  : Tot acc_t (decreases (if v end_ > v start then v end_ - v start else 0))
  = if v start >= v end_ then acc
    else foldi_range_impl (start +! mk_int 1) end_ (f acc start) f

let foldi_range #n #acc_t #inv r acc f =
  admit ();
  foldi_range_impl r.f_start r.f_end acc (fun a i -> f a i)

let rec foldi_range_step_by_impl (#n:inttype) (#acc_t:Type)
  (start end_: int_t n)
  (step: nat {step > 0 /\ range step n /\ range (v end_ + step) n})
  (acc: acc_t)
  (f: acc_t -> int_t n -> acc_t)
  : Tot acc_t (decreases (if v end_ > v start then v end_ - v start else 0))
  = if v start >= v end_ then acc
    else
      let next_v = v start + step in
      if next_v > v end_ then f acc start
      else foldi_range_step_by_impl (mk_int #n next_v) end_ step (f acc start) f

let foldi_range_step_by #n #acc_t #inv r step acc f =
  admit ();
  foldi_range_step_by_impl r.f_start r.f_end (v step) acc (fun a i -> f a i)

let rec foldi_chunks_exact_impl
  (#t #acc_t:Type)
  (s: t_Slice t)
  (chunk_len: nat {chunk_len > 0})
  (acc: acc_t)
  (f: acc_t -> (nat & list t) -> acc_t)
  (i: nat)
  : Tot acc_t (decreases (FStar.List.Tot.length s / chunk_len - i))
  = if i >= FStar.List.Tot.length s / chunk_len then acc
    else
      let chunk = Rust_primitives.Arrays.list_slice s (chunk_len * i) (chunk_len * (i + 1)) in
      foldi_chunks_exact_impl s chunk_len (f acc (i, chunk)) f (i + 1)

let foldi_chunks_exact #t #acc_t #inv s chunk_len acc f =
  admit ();
  foldi_chunks_exact_impl s (v chunk_len) acc (fun a (i, c) -> f a (sz i, c)) 0

let rec fold_chunks_exact_impl
  (#t #acc_t:Type)
  (s: t_Slice t)
  (chunk_len: nat {chunk_len > 0})
  (acc: acc_t)
  (f: acc_t -> list t -> acc_t)
  (i: nat)
  : Tot acc_t (decreases (FStar.List.Tot.length s / chunk_len - i))
  = if i >= FStar.List.Tot.length s / chunk_len then acc
    else
      let chunk = Rust_primitives.Arrays.list_slice s (chunk_len * i) (chunk_len * (i + 1)) in
      fold_chunks_exact_impl s chunk_len (f acc chunk) f (i + 1)

let fold_chunks_exact #t #acc_t #inv s chunk_len acc f =
  admit ();
  fold_chunks_exact_impl s (v chunk_len) acc (fun a c -> f a c) 0

let rec foldi_slice_impl (#t #acc_t:Type)
  (sl: list t)
  (acc: acc_t)
  (f: acc_t -> (nat & t) -> acc_t)
  (i: nat)
  : Tot acc_t (decreases (FStar.List.Tot.length sl - i))
  = if i >= FStar.List.Tot.length sl then acc
    else
      let item = FStar.List.Tot.index sl i in
      foldi_slice_impl sl (f acc (i, item)) f (i + 1)

let foldi_slice #t #acc_t #inv sl acc f =
  admit ();
  foldi_slice_impl sl acc (fun a (i, item) -> f a (sz i, item)) 0
