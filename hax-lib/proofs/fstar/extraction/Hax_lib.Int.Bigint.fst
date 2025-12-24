module Hax_lib.Int.Bigint
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Num_bigint.Bigint in
  ()

/// Maximal number of bytes stored in our copiable `BigInt`s.
let v_BYTES: usize = mk_usize 1024

type t_BigInt = {
  f_sign:Num_bigint.Bigint.t_Sign;
  f_data:t_Array u8 (mk_usize 1024)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_BigInt

unfold
let impl_5 = impl_5'

let impl_7: Core_models.Clone.t_Clone t_BigInt =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Marker.t_Copy t_BigInt

unfold
let impl_6 = impl_6'

/// Construct a [`BigInt`] from a [`num_bigint::BigInt`]. This
/// operation panics when the provided [`num_bigint::BigInt`]
/// has more than [`BYTES`] bytes.
let impl_BigInt__new (i: Num_bigint.Bigint.t_BigInt) : t_BigInt =
  let sign, bytes:(Num_bigint.Bigint.t_Sign & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Num_bigint.Bigint.impl_BigInt__to_bytes_be i
  in
  let _:Prims.unit =
    if (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global bytes <: usize) >. v_BYTES
    then
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic_fmt (Core_models.Fmt.Rt.impl_1__new_const
                (mk_usize 1)
                (let list =
                    ["`copiable_bigint::BigInt::new`: too big, please consider increasing `BYTES`"]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core_models.Fmt.t_Arguments)
          <:
          Rust_primitives.Hax.t_Never)
  in
  let data:t_Array u8 (mk_usize 1024) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1024) in
  let data:t_Array u8 (mk_usize 1024) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from data
      ({
          Core_models.Ops.Range.f_start
          =
          v_BYTES -! (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global bytes <: usize) <: usize
        }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (data.[ {
                Core_models.Ops.Range.f_start
                =
                v_BYTES -! (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global bytes <: usize) <: usize
              }
              <:
              Core_models.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          (bytes.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  { f_sign = sign; f_data = data } <: t_BigInt

/// Constructs a [`num_bigint::BigInt`] out of a [`BigInt`].
let impl_BigInt__get (self: t_BigInt) : Num_bigint.Bigint.t_BigInt =
  Num_bigint.Bigint.impl_BigInt__from_bytes_be self.f_sign (self.f_data <: t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Cmp.t_PartialEq t_BigInt t_BigInt =
  {
    f_eq_pre = (fun (self: t_BigInt) (other: t_BigInt) -> true);
    f_eq_post = (fun (self: t_BigInt) (other: t_BigInt) (out: bool) -> true);
    f_eq
    =
    fun (self: t_BigInt) (other: t_BigInt) ->
      (impl_BigInt__get self <: Num_bigint.Bigint.t_BigInt) =.
      (impl_BigInt__get other <: Num_bigint.Bigint.t_BigInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Cmp.t_Eq t_BigInt = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core_models.Cmp.t_PartialOrd t_BigInt t_BigInt =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_BigInt) (other: t_BigInt) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_BigInt)
        (other: t_BigInt)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_BigInt) (other: t_BigInt) ->
      Core_models.Cmp.f_partial_cmp #Num_bigint.Bigint.t_BigInt
        #Num_bigint.Bigint.t_BigInt
        #FStar.Tactics.Typeclasses.solve
        (impl_BigInt__get self <: Num_bigint.Bigint.t_BigInt)
        (impl_BigInt__get other <: Num_bigint.Bigint.t_BigInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Cmp.t_Ord t_BigInt =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_BigInt) (other: t_BigInt) -> true);
    f_cmp_post = (fun (self: t_BigInt) (other: t_BigInt) (out: Core_models.Cmp.t_Ordering) -> true);
    f_cmp
    =
    fun (self: t_BigInt) (other: t_BigInt) ->
      Core_models.Cmp.f_cmp #Num_bigint.Bigint.t_BigInt
        #FStar.Tactics.Typeclasses.solve
        (impl_BigInt__get self <: Num_bigint.Bigint.t_BigInt)
        (impl_BigInt__get other <: Num_bigint.Bigint.t_BigInt)
  }
