module Rust_primitives.Hax.Monomorphized_update_at_Lemmas

(** Lemmas about [update_at_*] operators that follow from the
    pre-/post-conditions in
    [Rust_primitives.Hax.Monomorphized_update_at] but require some
    [Seq] reasoning to discharge. *)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"

open Rust_primitives
open Rust_primitives.Hax
open Rust_primitives.Hax.Monomorphized_update_at
open Core_models.Ops.Range

(** Per-element view of [update_at_range]: the result agrees with
    [s] outside the [[i.f_start, i.f_end)] range and with [x]
    inside it.  Provable from the [Seq.slice] ensures of
    [update_at_range] plus [Seq.lemma_index_slice]. *)
let lemma_index_update_at_range
      #t (s: t_Slice t)
      (i: t_Range usize)
      (x: t_Slice t)
  : Lemma
      (requires
        v i.f_start >= 0 /\ v i.f_start <= Seq.length s /\
        v i.f_end <= Seq.length s /\
        Seq.length x == v i.f_end - v i.f_start)
      (ensures (
        let out = update_at_range s i x in
        Seq.length out == Seq.length s /\
        (forall (j: nat).
            (j < v i.f_start ==> Seq.index out j == Seq.index s j) /\
            (j >= v i.f_start /\ j < v i.f_end ==>
                Seq.index out j == Seq.index x (j - v i.f_start)) /\
            (j >= v i.f_end /\ j < Seq.length out ==>
                Seq.index out j == Seq.index s j))))
  = let out = update_at_range s i x in
    let aux (j: nat) :
      Lemma
        ((j < v i.f_start ==> Seq.index out j == Seq.index s j) /\
         (j >= v i.f_start /\ j < v i.f_end ==>
             Seq.index out j == Seq.index x (j - v i.f_start)) /\
         (j >= v i.f_end /\ j < Seq.length out ==>
             Seq.index out j == Seq.index s j))
      = if j < v i.f_start then
          // Seq.slice out 0 i.f_start == Seq.slice s 0 i.f_start
          (Seq.lemma_index_slice out 0 (v i.f_start) j;
           Seq.lemma_index_slice s 0 (v i.f_start) j)
        else if j < v i.f_end && j >= v i.f_start then
          // Seq.slice out i.f_start i.f_end == x
          (Seq.lemma_index_slice out (v i.f_start) (v i.f_end) (j - v i.f_start))
        else if j >= v i.f_end && j < Seq.length out then
          // Seq.slice out i.f_end (length out) == Seq.slice s i.f_end (length s)
          (Seq.lemma_index_slice out (v i.f_end) (Seq.length out) (j - v i.f_end);
           Seq.lemma_index_slice s (v i.f_end) (Seq.length s) (j - v i.f_end))
        else
          ()
    in
    FStar.Classical.forall_intro aux
