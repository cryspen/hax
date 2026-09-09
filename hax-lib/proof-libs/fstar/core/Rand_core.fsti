module Rand_core
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_RngCore (v_Self: Type0) = {
  f_next_u32_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_next_u32_post:v_Self -> (v_Self & u32) -> Type0;
  f_next_u32:x0: v_Self
    -> Prims.Pure (v_Self & u32) (f_next_u32_pre x0) (fun result -> f_next_u32_post x0 result);
  f_next_u64_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_next_u64_post:v_Self -> (v_Self & u64) -> Type0;
  f_next_u64:x0: v_Self
    -> Prims.Pure (v_Self & u64) (f_next_u64_pre x0) (fun result -> f_next_u64_post x0 result);
  f_fill_bytes_pre:self_: v_Self -> dst: t_Slice u8 -> pred: Type0{true ==> pred};
  f_fill_bytes_post:self_: v_Self -> dst: t_Slice u8 -> x: (v_Self & t_Slice u8)
    -> pred:
      Type0
        { pred ==>
          (let (self_e_future: v_Self), (dst_future: t_Slice u8) = x in
            (Core_models.Slice.impl__len #u8 dst_future <: usize) =.
            (Core_models.Slice.impl__len #u8 dst <: usize)) };
  f_fill_bytes:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & t_Slice u8)
        (f_fill_bytes_pre x0 x1)
        (fun result -> f_fill_bytes_post x0 x1 result)
}

class t_CryptoRng (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_RngCore v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_CryptoRng v_Self|} -> i._super_i0
