module Rust_primitives.Hax.Folds

open Rust_primitives
open Core_models.Ops.Range
open FStar.Mul

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let rec fold_enumerated_chunked_slice_aux
  (#t: Type0) (#acc_t: Type0)
  (chunk_size: usize {v chunk_size > 0})
  (s: t_Slice t)
  (inv: acc_t -> (i:usize{v i <= FStar.List.Tot.length s / v chunk_size}) -> Type0)
  (acc: acc_t)
  (f: ( acc:acc_t
      -> item:(usize & t_Slice t) {
        let (i, s_chunk) = item in
          v i < FStar.List.Tot.length s / v chunk_size
        /\ length s_chunk == chunk_size
        /\ nth_chunk_of s s_chunk (v i)
        /\ inv acc i
      }
      -> acc':acc_t {
        inv acc' (fst item +! sz 1)
      }
      )
  )
  (i: nat {i <= FStar.List.Tot.length s / v chunk_size})
  : Tot acc_t (decreases (FStar.List.Tot.length s / v chunk_size - i))
  = if i = FStar.List.Tot.length s / v chunk_size then acc
    else
      let chunk = Rust_primitives.Arrays.list_slice s (v chunk_size * i) (v chunk_size * (i + 1)) in
      assume (inv acc (sz i));
      assume (nth_chunk_of s chunk i);
      let acc' = f acc (sz i, chunk) in
      fold_enumerated_chunked_slice_aux chunk_size s inv acc' f (i + 1)

let fold_enumerated_chunked_slice #t #acc_t chunk_size s inv init f =
  admit (); // postcondition: inv result (length s / chunk_size)
  fold_enumerated_chunked_slice_aux chunk_size s inv init f 0

let rec fold_chunked_slice_aux
  (#t: Type0) (#acc_t: Type0)
  (chunk_size: usize {v chunk_size > 0})
  (s: t_Slice t)
  (inv: acc_t -> (i:usize) -> Type0)
  (acc: acc_t)
  (f: ( acc:acc_t
      -> item:(t_Slice t) {
        length item == chunk_size /\
        inv acc (sz 0)
      }
      -> acc':acc_t {
        inv acc' (sz 0)
      }
      )
  )
  (i: nat {i <= FStar.List.Tot.length s / v chunk_size})
  : Tot acc_t (decreases (FStar.List.Tot.length s / v chunk_size - i))
  = if i = FStar.List.Tot.length s / v chunk_size then acc
    else
      let chunk = Rust_primitives.Arrays.list_slice s (v chunk_size * i) (v chunk_size * (i + 1)) in
      assume (inv acc (sz 0));
      let acc' = f acc chunk in
      fold_chunked_slice_aux chunk_size s inv acc' f (i + 1)

let fold_chunked_slice #t #acc_t chunk_size s inv init f =
  admit (); // postcondition
  fold_chunked_slice_aux chunk_size s inv init f 0

let rec fold_enumerated_slice_aux
  (#t: Type0) (#acc_t: Type0)
  (s: t_Slice t)
  (inv: acc_t -> (i:usize{v i <= v (length s)}) -> Type0)
  (acc: acc_t)
  (f: (acc:acc_t -> i:(usize & t) {v (fst i) < v (length s) /\ snd i == FStar.List.Tot.index s (v (fst i)) /\ inv acc  (fst i)}
                 -> acc':acc_t    {v (fst i) < v (length s) /\ inv acc' (fst i)}))
  (i: nat {i <= FStar.List.Tot.length s})
  : Tot acc_t (decreases (FStar.List.Tot.length s - i))
  = if i = FStar.List.Tot.length s then acc
    else
      let item = FStar.List.Tot.index s i in
      assume (inv acc (sz i));
      let acc' = f acc (sz i, item) in
      fold_enumerated_slice_aux s inv acc' f (i + 1)

let fold_enumerated_slice #t #acc_t s inv init f =
  admit (); // postcondition
  fold_enumerated_slice_aux s inv init f 0

let fold_enumerated_slice_return #t #acc_t #ret s inv init f =
  admit () // TODO: implement with early return support

let rec fold_range_step_by_aux
  (#acc_t: Type0) (#u: inttype)
  (start: int_t u) (end_: int_t u)
  (step: usize {v step > 0 /\ range (v end_ + v step) u})
  (inv: acc_t -> (i:int_t u{fold_range_step_by_wf_index start end_ step false (v i)}) -> Type0)
  (acc: acc_t)
  (f: (acc:acc_t -> i:int_t u  {v i < v end_ - ((v end_ - 1 - v start) % v step) /\ fold_range_step_by_wf_index start end_ step true (v i) /\ inv acc i}
                 -> acc':acc_t {(inv acc' (mk_int (v i + v step)))}))
  (cur: int_t u {v cur >= v start /\ v cur <= v end_})
  : Tot acc_t (decreases (v end_ - v cur))
  = if v cur >= v end_ then acc
    else begin
      assume (fold_range_step_by_wf_index start end_ step true (v cur));
      assume (inv acc cur);
      assume (v cur < v end_ - ((v end_ - 1 - v start) % v step));
      let acc' = f acc cur in
      assume (Rust_primitives.Integers.range (v step) u);
      let next = cur +! (mk_int #u (v step)) in
      if v next >= v end_ then acc'
      else fold_range_step_by_aux start end_ step inv acc' f next
    end

let fold_range_step_by #acc_t #u start end_ step inv init f =
  admit (); // postcondition
  if v start < v end_
  then fold_range_step_by_aux start end_ step inv init f start
  else init

let fold_return #it #acc #ret #item (i: it) (init: acc) f =
  admit () // TODO: implement generic fold with early return
