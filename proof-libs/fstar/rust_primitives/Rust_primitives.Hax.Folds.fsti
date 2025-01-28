module Rust_primitives.Hax.Folds

open Rust_primitives
open Core.Ops.Range
open FStar.Mul

(**** `s.chunks_exact(chunk_size).enumerate()` *)
/// Predicate that asserts a slice `s_chunk` is exactly the nth chunk
/// of the sequence `s`
let nth_chunk_of #t
  (s: Seq.seq t)
  (s_chunk: Seq.seq t {Seq.length s_chunk > 0})
  (chunk_nth: nat {chunk_nth < Seq.length s / Seq.length s_chunk})
  =  Seq.slice s (Seq.length s_chunk * chunk_nth) (Seq.length s_chunk * (chunk_nth + 1))
  == s_chunk

#push-options "--z3rlimit 90"
let rec fold_enumerated_chunked_slice_aux
  (#t: Type0) (#acc_t: Type0)
  (chunk_size: usize {v chunk_size > 0})
  (s: t_Slice t {Seq.length s % v chunk_size = 0})
  (inv: acc_t -> (i:nat{i <= Seq.length s / v chunk_size}) -> Type0)
  (i: nat{i <= Seq.length s / v chunk_size})
  (init: acc_t {inv init i})
  (f: ( acc:acc_t
      -> item:(usize & t_Slice t) {
        let (i, s_chunk) = item in
          v i < Seq.length s / v chunk_size
        /\ length s_chunk == chunk_size
        /\ nth_chunk_of s s_chunk (v i)
        /\ inv acc (v i)
      }
      -> acc':acc_t {
        inv acc' (v (fst item) + 1)
      }
      )
  )
  : Tot (result: acc_t {inv result (Seq.length s / v chunk_size)})
        (decreases (Seq.length s / v chunk_size) - i)
  = let num_chunks = Seq.length s / v chunk_size in
    if i = num_chunks then init else begin
      FStar.Math.Lemmas.lemma_mult_lt_right (v chunk_size) i num_chunks;
      let start = i * v chunk_size in
      let end_ = (i + 1) * v chunk_size in
      let s_chunk = Seq.slice s start end_ in
      let init' = f init (mk_int i, s_chunk) in
      fold_enumerated_chunked_slice_aux chunk_size s inv (i + 1) init' f
    end
#pop-options

/// Fold function that is generated for `for` loops iterating on
/// `s.chunks_exact(chunk_size).enumerate()`-like iterators
let fold_enumerated_chunked_slice
  (#t: Type0) (#acc_t: Type0)
  (chunk_size: usize {v chunk_size > 0})
  (s: t_Slice t {Seq.length s % v chunk_size = 0})
  (inv: acc_t -> (i:usize{v i <= Seq.length s / v chunk_size}) -> Type0)
  (init: acc_t {inv init (sz 0)})
  (f: ( acc:acc_t
      -> item:(usize & t_Slice t) {
        let (i, s_chunk) = item in
          v i < Seq.length s / v chunk_size
        /\ length s_chunk == chunk_size
        /\ nth_chunk_of s s_chunk (v i)
        /\ inv acc i
      }
      -> acc':acc_t {
        inv acc' (fst item +! sz 1)
      }
      )
  )
  : result: acc_t {inv result (mk_int (Seq.length s / v chunk_size))}
  = fold_enumerated_chunked_slice_aux chunk_size s (fun acc i -> inv acc (mk_int i)) 0 init f

open Core.Ops
open Core.Ops.Index
open Rust_primitives

type t_Coefficients = {
  f_values: t_Array i32 (mk_int 8)
}

#push-options "--z3rlimit 80"
let serialize
      (simd_unit: t_Coefficients)
      (serialized: t_Slice u8 {Seq.length serialized <= 6})
     =
  let serialized:t_Slice u8 =
    match cast (Core.Slice.impl__len #u8 serialized <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 4 ->
      let serialized:t_Slice u8 =
        fold_enumerated_chunked_slice (mk_usize 2)
          (simd_unit.f_values <: t_Slice i32)
          (fun serialized temp_1_ ->
              let serialized:t_Slice u8 = serialized in
              let _:usize = temp_1_ in
              Seq.length serialized == 4)
          serialized
          (fun serialized temp_1_ ->
              let serialized:t_Slice u8 = serialized in
              let i, coefficients:(usize & t_Slice i32) = temp_1_ in
              let coefficient0:u8 = cast (Seq.index coefficients 0 <: i32) <: u8 in
              let coefficient1:u8 = cast (Seq.index coefficients 1 <: i32) <: u8 in
              assert (v i < 4);
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  i
                  ((coefficient1 <<! mk_i32 4 <: u8) |. coefficient0 <: u8)
              in
              serialized)
      in
      serialized
    | Rust_primitives.Integers.MkInt 6 ->
      let serialized:t_Slice u8 =
        fold_enumerated_chunked_slice (mk_usize 4)
          (simd_unit.f_values <: t_Slice i32)
          (fun serialized temp_1_ ->
              let serialized:t_Slice u8 = serialized in
              let _:usize = temp_1_ in
              Seq.length serialized == 6)
          serialized
          (fun serialized temp_1_ ->
              let serialized:t_Slice u8 = serialized in
              let i, coefficients:(usize & t_Slice i32) = temp_1_ in
              let coefficient0:u8 = cast (Seq.index coefficients 0 <: i32) <: u8 in
              let coefficient1:u8 = cast (Seq.index coefficients 1 <: i32) <: u8 in
              let coefficient2:u8 = cast (Seq.index coefficients 2 <: i32) <: u8 in
              let coefficient3:u8 = cast (Seq.index coefficients 3 <: i32) <: u8 in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  (mk_usize 3 *! i <: usize)
                  ((coefficient1 <<! mk_i32 6 <: u8) |. coefficient0 <: u8)
              in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  ((mk_usize 3 *! i <: usize) +! mk_usize 1 <: usize)
                  ((coefficient2 <<! mk_i32 4 <: u8) |. (coefficient1 >>! mk_i32 2 <: u8) <: u8)
              in
              let serialized:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
                  ((mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize)
                  ((coefficient3 <<! mk_i32 2 <: u8) |. (coefficient2 >>! mk_i32 4 <: u8) <: u8)
              in
              serialized)
      in
      serialized
    | _ -> serialized
  in
  serialized
#pop-options

(**** `s.enumerate()` *)
/// Fold function that is generated for `for` loops iterating on
/// `s.enumerate()`-like iterators
val fold_enumerated_slice
  (#t: Type0) (#acc_t: Type0)
  (s: t_Slice t)
  (inv: acc_t -> (i:usize{v i <= v (length s)}) -> Type0)
  (init: acc_t {inv init (sz 0)})
  (f: (acc:acc_t -> i:(usize & t) {v (fst i) < v (length s) /\ snd i == Seq.index s (v (fst i)) /\ inv acc  (fst i)}
                 -> acc':acc_t    {v (fst i) < v (length s) /\ inv acc' (fst i)}))
  : result: acc_t {inv result (length s)}

(**** `(start..end_).step_by(step)` *)
unfold let fold_range_step_by_wf_index (#u: inttype)
  (start: int_t u) (end_: int_t u)
  (step: usize {v step > 0}) (strict: bool) (i: int)
  = v start < v end_ ==> (let end_step = v end_ - 1 - ((v end_ - 1 - v start) % v step) in
                          i >= v start 
                        /\ (if strict then i <= end_step else i <= end_step + v step))
  // /\ i % v step == v start % v step

#push-options "--z3rlimit 80"
unfold let fold_range_step_by_upper_bound (#u: inttype)
  (start: int_t u) (end_: int_t u)
  (step: usize {v step > 0})
  : end':int {fold_range_step_by_wf_index start end_ step false end'}
  = if v end_ <= v start 
    then v end_
    else
      let range: nat = v end_ - v start in
      let k: nat = range / v step in
      let end' = v start + k * v step in
      FStar.Math.Lemmas.division_propriety range (v step);
      end'
#pop-options

/// Fold function that is generated for `for` loops iterating on
/// `s.enumerate()`-like iterators
val fold_range_step_by
  (#acc_t: Type0) (#u: inttype)
  (start: int_t u)
  (end_: int_t u)
  (step: usize {v step > 0 /\ range (v end_ + v step) u})
  (inv: acc_t -> (i:int_t u{fold_range_step_by_wf_index start end_ step false (v i)}) -> Type0)
  (init: acc_t {inv init start})
  (f: (acc:acc_t -> i:int_t u  {v i < v end_ - ((v end_ - 1 - v start) % v step) /\ fold_range_step_by_wf_index start end_ step true (v i) /\ inv acc i}
                 -> acc':acc_t {(inv acc' (mk_int (v i + v step)))}))
  : result: acc_t {inv result (mk_int (fold_range_step_by_upper_bound start end_ step))}

(**** `start..end_` *)
unfold let fold_range_wf_index (#u: inttype)
  (start: int_t u) (end_: int_t u)
  (strict: bool) (i: int)
  = v start <= v end_
  ==> ( i >= v start 
     /\ (if strict then i < v end_ else i <= v end_))

let rec fold_range
  (#acc_t: Type0) (#u: inttype)
  (start: int_t u)
  (end_: int_t u)
  (inv: acc_t -> (i:int_t u{fold_range_wf_index start end_ false (v i)}) -> Type0)
  (init: acc_t {inv init start})
  (f: (acc:acc_t -> i:int_t u  {v i <= v end_ /\ fold_range_wf_index start end_ true (v i) /\ inv acc i}
                 -> acc':acc_t {(inv acc' (mk_int (v i + 1)))}))
  : Tot (result: acc_t {inv result (if v start > v end_ then start else end_)}) 
        (decreases v end_ - v start)
  = if v start < v end_
    then fold_range (start +! mk_int 1) end_ inv (f init start) f
    else init

let rec fold_range_cf
  (#acc_t: Type0) (#u: inttype)
  (start: int_t u)
  (end_: int_t u)
  (inv: acc_t -> (i:int_t u{fold_range_wf_index start end_ false (v i)}) -> Type0)
  (acc: acc_t )
  (f: (acc:acc_t -> i:int_t u {v i <= v end_ /\ fold_range_wf_index start end_ true (v i) }
                  -> tuple:((Core.Ops.Control_flow.t_ControlFlow (unit & acc_t) acc_t))
                    {
                      let acc = match tuple with 
                        | Core.Ops.Control_flow.ControlFlow_Break ((), acc)
                        | Core.Ops.Control_flow.ControlFlow_Continue acc -> acc in
                      inv acc (mk_int (v i + 1))}))
: Tot acc_t (decreases v end_ - v start)
  =
  if v start < v end_
  then match f acc start with
       | Core.Ops.Control_flow.ControlFlow_Break ((), acc) -> acc
       | Core.Ops.Control_flow.ControlFlow_Continue acc ->
         fold_range_cf (start +! mk_int 1) end_ inv acc f
  else acc

let rec fold_range_return
  (#acc_t: Type0) (#ret_t: Type0) (#u: inttype)
  (start: int_t u)
  (end_: int_t u)
  (inv: acc_t -> (i:int_t u{fold_range_wf_index start end_ false (v i)}) -> Type0)
  (acc: acc_t )
  (f: (acc:acc_t -> i:int_t u {v i <= v end_ /\ fold_range_wf_index start end_ true (v i) }
                  -> tuple:((Core.Ops.Control_flow.t_ControlFlow (Core.Ops.Control_flow.t_ControlFlow ret_t (unit & acc_t))) acc_t)
                    ))
: Tot (Core.Ops.Control_flow.t_ControlFlow ret_t acc_t) (decreases v end_ - v start)
  =
  if v start < v end_
  then match f acc start with
       | Core.Ops.Control_flow.ControlFlow_Break (Core.Ops.Control_flow.ControlFlow_Break res)-> Core.Ops.Control_flow.ControlFlow_Break res
       
       | Core.Ops.Control_flow.ControlFlow_Break (Core.Ops.Control_flow.ControlFlow_Continue ((), res)) -> Core.Ops.Control_flow.ControlFlow_Continue res
       | Core.Ops.Control_flow.ControlFlow_Continue acc ->
         fold_range_return (start +! mk_int 1) end_ inv acc f
  else Core.Ops.Control_flow.ControlFlow_Continue acc
