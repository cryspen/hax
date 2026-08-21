module Core_models.Hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::hash::Hasher`]
/// Real `core` supplies every `write_*` method as a trait *default* on top of
/// `write`; hax does not support trait defaults, so they are required methods
/// here and every `Hasher` implementation spells them out. The doc comment on
/// each one names the `core` method it mirrors, and the bodies an implementation
/// is expected to give are exactly `core`'s defaults.
class t_Hasher (v_Self: Type0) = {
  f_finish_pre:v_Self -> Type0;
  f_finish_post:v_Self -> u64 -> Type0;
  f_finish:x0: v_Self -> Prims.Pure u64 (f_finish_pre x0) (fun result -> f_finish_post x0 result);
  f_write_pre:v_Self -> t_Slice u8 -> Type0;
  f_write_post:v_Self -> t_Slice u8 -> v_Self -> Type0;
  f_write:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure v_Self (f_write_pre x0 x1) (fun result -> f_write_post x0 x1 result);
  f_write_u8_pre:v_Self -> u8 -> Type0;
  f_write_u8_post:v_Self -> u8 -> v_Self -> Type0;
  f_write_u8:x0: v_Self -> x1: u8
    -> Prims.Pure v_Self (f_write_u8_pre x0 x1) (fun result -> f_write_u8_post x0 x1 result);
  f_write_u16_pre:v_Self -> u16 -> Type0;
  f_write_u16_post:v_Self -> u16 -> v_Self -> Type0;
  f_write_u16:x0: v_Self -> x1: u16
    -> Prims.Pure v_Self (f_write_u16_pre x0 x1) (fun result -> f_write_u16_post x0 x1 result);
  f_write_u32_pre:v_Self -> u32 -> Type0;
  f_write_u32_post:v_Self -> u32 -> v_Self -> Type0;
  f_write_u32:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_write_u32_pre x0 x1) (fun result -> f_write_u32_post x0 x1 result);
  f_write_u64_pre:v_Self -> u64 -> Type0;
  f_write_u64_post:v_Self -> u64 -> v_Self -> Type0;
  f_write_u64:x0: v_Self -> x1: u64
    -> Prims.Pure v_Self (f_write_u64_pre x0 x1) (fun result -> f_write_u64_post x0 x1 result);
  f_write_u128_pre:v_Self -> u128 -> Type0;
  f_write_u128_post:v_Self -> u128 -> v_Self -> Type0;
  f_write_u128:x0: v_Self -> x1: u128
    -> Prims.Pure v_Self (f_write_u128_pre x0 x1) (fun result -> f_write_u128_post x0 x1 result);
  f_write_usize_pre:v_Self -> usize -> Type0;
  f_write_usize_post:v_Self -> usize -> v_Self -> Type0;
  f_write_usize:x0: v_Self -> x1: usize
    -> Prims.Pure v_Self (f_write_usize_pre x0 x1) (fun result -> f_write_usize_post x0 x1 result);
  f_write_i8_pre:v_Self -> i8 -> Type0;
  f_write_i8_post:v_Self -> i8 -> v_Self -> Type0;
  f_write_i8:x0: v_Self -> x1: i8
    -> Prims.Pure v_Self (f_write_i8_pre x0 x1) (fun result -> f_write_i8_post x0 x1 result);
  f_write_i16_pre:v_Self -> i16 -> Type0;
  f_write_i16_post:v_Self -> i16 -> v_Self -> Type0;
  f_write_i16:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self (f_write_i16_pre x0 x1) (fun result -> f_write_i16_post x0 x1 result);
  f_write_i32_pre:v_Self -> i32 -> Type0;
  f_write_i32_post:v_Self -> i32 -> v_Self -> Type0;
  f_write_i32:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self (f_write_i32_pre x0 x1) (fun result -> f_write_i32_post x0 x1 result);
  f_write_i64_pre:v_Self -> i64 -> Type0;
  f_write_i64_post:v_Self -> i64 -> v_Self -> Type0;
  f_write_i64:x0: v_Self -> x1: i64
    -> Prims.Pure v_Self (f_write_i64_pre x0 x1) (fun result -> f_write_i64_post x0 x1 result);
  f_write_i128_pre:v_Self -> i128 -> Type0;
  f_write_i128_post:v_Self -> i128 -> v_Self -> Type0;
  f_write_i128:x0: v_Self -> x1: i128
    -> Prims.Pure v_Self (f_write_i128_pre x0 x1) (fun result -> f_write_i128_post x0 x1 result);
  f_write_isize_pre:v_Self -> isize -> Type0;
  f_write_isize_post:v_Self -> isize -> v_Self -> Type0;
  f_write_isize:x0: v_Self -> x1: isize
    -> Prims.Pure v_Self (f_write_isize_pre x0 x1) (fun result -> f_write_isize_post x0 x1 result);
  f_write_length_prefix_pre:v_Self -> usize -> Type0;
  f_write_length_prefix_post:v_Self -> usize -> v_Self -> Type0;
  f_write_length_prefix:x0: v_Self -> x1: usize
    -> Prims.Pure v_Self
        (f_write_length_prefix_pre x0 x1)
        (fun result -> f_write_length_prefix_post x0 x1 result);
  f_write_str_pre:v_Self -> string -> Type0;
  f_write_str_post:v_Self -> string -> v_Self -> Type0;
  f_write_str:x0: v_Self -> x1: string
    -> Prims.Pure v_Self (f_write_str_pre x0 x1) (fun result -> f_write_str_post x0 x1 result)
}

/// See [`std::hash::BuildHasherDefault`]
type t_BuildHasherDefault (v_H: Type0) =
  | BuildHasherDefault : Core_models.Marker.t_PhantomData v_H -> t_BuildHasherDefault v_H

/// See [`std::hash::BuildHasherDefault::new`]
val impl__new: #v_H: Type0 -> Prims.unit
  -> Prims.Pure (t_BuildHasherDefault v_H) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::hash::Hash`]
class t_Hash (v_Self: Type0) = {
  f_hash_pre:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> self_: v_Self -> h: v_H
    -> pred: Type0{true ==> pred};
  f_hash_post:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> v_Self -> v_H -> v_H -> Type0;
  f_hash:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> x0: v_Self -> x1: v_H
    -> Prims.Pure v_H (f_hash_pre #v_H #i1 x0 x1) (fun result -> f_hash_post #v_H #i1 x0 x1 result);
  f_hash_slice_pre:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> t_Slice v_Self -> v_H -> Type0;
  f_hash_slice_post:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> t_Slice v_Self -> v_H -> v_H -> Type0;
  f_hash_slice:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> x0: t_Slice v_Self -> x1: v_H
    -> Prims.Pure v_H
        (f_hash_slice_pre #v_H #i1 x0 x1)
        (fun result -> f_hash_slice_post #v_H #i1 x0 x1 result)
}

/// See [`std::hash::BuildHasher`]
class t_BuildHasher (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Hasher:Type0;
  f_Hasher_i0:t_Hasher f_Hasher;
  f_build_hasher_pre:v_Self -> Type0;
  f_build_hasher_post:v_Self -> f_Hasher -> Type0;
  f_build_hasher:x0: v_Self
    -> Prims.Pure f_Hasher (f_build_hasher_pre x0) (fun result -> f_build_hasher_post x0 result);
  f_hash_one_pre:#v_T: Type0 -> {| i1: t_Hash v_T |} -> v_Self -> v_T -> Type0;
  f_hash_one_post:#v_T: Type0 -> {| i1: t_Hash v_T |} -> v_Self -> v_T -> u64 -> Type0;
  f_hash_one:#v_T: Type0 -> {| i1: t_Hash v_T |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure u64
        (f_hash_one_pre #v_T #i1 x0 x1)
        (fun result -> f_hash_one_post #v_T #i1 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Hash_for_u8:t_Hash u8

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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_H)
    : t_BuildHasher (t_BuildHasherDefault v_H) =
  {
    f_Hasher = v_H;
    f_Hasher_i0 = FStar.Tactics.Typeclasses.solve;
    f_build_hasher_pre = (fun (self: t_BuildHasherDefault v_H) -> true);
    f_build_hasher_post = (fun (self: t_BuildHasherDefault v_H) (out: v_H) -> true);
    f_build_hasher
    =
    (fun (self: t_BuildHasherDefault v_H) ->
        Core_models.Default.f_default #v_H #FStar.Tactics.Typeclasses.solve ());
    f_hash_one_pre
    =
    (fun
        (#v_T: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_T)
        (self: t_BuildHasherDefault v_H)
        (x: v_T)
        ->
        true);
    f_hash_one_post
    =
    (fun
        (#v_T: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_T)
        (self: t_BuildHasherDefault v_H)
        (x: v_T)
        (out: u64)
        ->
        true);
    f_hash_one
    =
    fun
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_T)
      (self: t_BuildHasherDefault v_H)
      (x: v_T)
      ->
      f_finish #v_H
        #FStar.Tactics.Typeclasses.solve
        (f_hash #v_T
            #FStar.Tactics.Typeclasses.solve
            #v_H
            x
            (f_build_hasher #(t_BuildHasherDefault v_H) #FStar.Tactics.Typeclasses.solve self <: v_H
            )
          <:
          v_H)
  }
