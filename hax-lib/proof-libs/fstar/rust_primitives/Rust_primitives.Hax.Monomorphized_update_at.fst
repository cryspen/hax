module Rust_primitives.Hax.Monomorphized_update_at

open Rust_primitives
open Rust_primitives.Hax
open Core_models.Ops.Range

#set-options "--z3rlimit 30 --fuel 1"

let update_at_range #n (#t: Type0) (s: t_Slice t) (i: t_Range (int_t n)) (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_start >= 0 /\ v i.f_start <= FStar.List.Tot.length s /\
               v i.f_end <= FStar.List.Tot.length s /\
               FStar.List.Tot.length x == v i.f_end - v i.f_start))
    (ensures (fun res ->
                Rust_primitives.Arrays.list_slice res 0 (v i.f_start) == Rust_primitives.Arrays.list_slice s 0 (v i.f_start) /\
                Rust_primitives.Arrays.list_slice res (v i.f_start) (v i.f_end) == x /\
                Rust_primitives.Arrays.list_slice res (v i.f_end) (FStar.List.Tot.length res) == Rust_primitives.Arrays.list_slice s (v i.f_end) (FStar.List.Tot.length s)))
  = let prefix = Rust_primitives.Arrays.list_slice s 0 (v i.f_start) in
    let suffix = Rust_primitives.Arrays.list_slice s (v i.f_end) (FStar.List.Tot.length s) in
    FStar.List.Tot.Properties.append_length prefix x;
    FStar.List.Tot.Properties.append_length (FStar.List.Tot.append prefix x) suffix;
    let result = FStar.List.Tot.append (FStar.List.Tot.append prefix x) suffix in
    assume (Rust_primitives.Arrays.list_slice result 0 (v i.f_start) == prefix);
    assume (Rust_primitives.Arrays.list_slice result (v i.f_start) (v i.f_end) == x);
    assume (Rust_primitives.Arrays.list_slice result (v i.f_end) (FStar.List.Tot.length result) == suffix);
    result

let update_at_range_to #n (#t: Type0) (s: t_Slice t) (i: t_RangeTo (int_t n)) (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_end >= 0 /\ v i.f_end <= FStar.List.Tot.length s /\
               FStar.List.Tot.length x == v i.f_end))
    (ensures (fun res ->
                Rust_primitives.Arrays.list_slice res 0 (v i.f_end) == x /\
                Rust_primitives.Arrays.list_slice res (v i.f_end) (FStar.List.Tot.length res) == Rust_primitives.Arrays.list_slice s (v i.f_end) (FStar.List.Tot.length s)))
  = let suffix = Rust_primitives.Arrays.list_slice s (v i.f_end) (FStar.List.Tot.length s) in
    FStar.List.Tot.Properties.append_length x suffix;
    let result = FStar.List.Tot.append x suffix in
    assume (Rust_primitives.Arrays.list_slice result 0 (v i.f_end) == x);
    assume (Rust_primitives.Arrays.list_slice result (v i.f_end) (FStar.List.Tot.length result) == suffix);
    result

let update_at_range_from #n (#t: Type0) (s: t_Slice t) (i: t_RangeFrom (int_t n)) (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires ( v i.f_start >= 0 /\ v i.f_start <= FStar.List.Tot.length s /\
                FStar.List.Tot.length x == FStar.List.Tot.length s - v i.f_start))
    (ensures (fun res ->
                Rust_primitives.Arrays.list_slice res 0 (v i.f_start) == Rust_primitives.Arrays.list_slice s 0 (v i.f_start) /\
                Rust_primitives.Arrays.list_slice res (v i.f_start) (FStar.List.Tot.length res) == x))
  = let prefix = Rust_primitives.Arrays.list_slice s 0 (v i.f_start) in
    FStar.List.Tot.Properties.append_length prefix x;
    let result = FStar.List.Tot.append prefix x in
    assume (Rust_primitives.Arrays.list_slice result 0 (v i.f_start) == prefix);
    assume (Rust_primitives.Arrays.list_slice result (v i.f_start) (FStar.List.Tot.length result) == x);
    result

let update_at_range_full (#t: Type0) (s: t_Slice t) (i: t_RangeFull) (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (FStar.List.Tot.length x == FStar.List.Tot.length s))
    (ensures (fun res -> res == x))
  = x
