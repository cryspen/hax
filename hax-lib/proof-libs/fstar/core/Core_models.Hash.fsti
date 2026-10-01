module Core_models.Hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::hash::Hasher`]
class t_Hasher (v_Self: Type0) = {
  f_finish_pre:v_Self -> Type0;
  f_finish_post:v_Self -> u64 -> Type0;
  f_finish:x0: v_Self -> Prims.Pure u64 (f_finish_pre x0) (fun result -> f_finish_post x0 result);
  f_write_pre:v_Self -> t_Slice u8 -> Type0;
  f_write_post:v_Self -> t_Slice u8 -> v_Self -> Type0;
  f_write:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure v_Self (f_write_pre x0 x1) (fun result -> f_write_post x0 x1 result)
}

/// See [`std::hash::Hash`]
class t_Hash (v_Self: Type0) = {
  f_hash_pre:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> self_: v_Self -> h: v_H
    -> pred: Type0{true ==> pred};
  f_hash_post:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> v_Self -> v_H -> v_H -> Type0;
  f_hash:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> x0: v_Self -> x1: v_H
    -> Prims.Pure v_H (f_hash_pre #v_H #i1 x0 x1) (fun result -> f_hash_post #v_H #i1 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_Hash u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_u16:t_Hash u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_u32:t_Hash u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_u64:t_Hash u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_u128:t_Hash u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_usize:t_Hash usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_i8:t_Hash i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_i16:t_Hash i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_i32:t_Hash i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_i64:t_Hash i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_i128:t_Hash i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_isize:t_Hash isize
