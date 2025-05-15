module Rust_primitives.Hax.Monomorphized_update_at
#set-options "--z3rlimit 30"

/// Monomorphized versions of the `update_at` operator.

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range

let update_at_usize
  (#t: Type0)
  (s: t_Slice t)
  (i: usize {i <. length s})
  (x: t)
  : t_Array t (length s)
  = upd #t s i x

val update_at_range #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_Range (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_start >= 0 /\ 
               v i.f_start <= v (length s) /\
               v i.f_end <= v (length s) /\
               v (length x) == v i.f_end - v i.f_start))
    (ensures (fun res ->
                slice res (sz 0) (sz (v i.f_start)) == slice s (sz 0) (sz (v i.f_start)) /\
                slice res (sz (v i.f_start)) (sz (v i.f_end)) == x /\
                slice res (sz (v i.f_end)) (length res) == slice s (sz (v i.f_end)) (length s)))

val update_at_range_to #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeTo (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_end >= 0 /\ v i.f_end <= v (length s) /\
               v (length x) == v i.f_end))
    (ensures (fun res ->
                slice res (sz 0) (sz (v i.f_end)) == x /\
                slice res (sz (v i.f_end)) (length res) == slice s (sz (v i.f_end)) (length s)))

val update_at_range_from #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeFrom (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires ( v i.f_start >= 0 /\ v i.f_start <= v (length s) /\
                v (length x) == v (length s) - v i.f_start))
    (ensures (fun res ->
                slice res (sz 0) (sz (v i.f_start)) == slice s (sz 0) (sz (v i.f_start)) /\
                slice res (sz (v i.f_start)) (length res) == x))

val update_at_range_full
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeFull)
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (length x == length s))
    (ensures (fun res -> res == x))
