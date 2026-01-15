module Tests.Legacy__attributes.Verifcation_status
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

#push-options "--admit_smt_queries true"

let a_function_which_only_laxes (_: Prims.unit) : Prims.unit = Hax_lib.v_assert false

#pop-options

let a_panicfree_function (_: Prims.unit)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun x ->
          let x:u8 = x in
          false) =
  let a:u8 = mk_u8 3 in
  let b:u8 = mk_u8 6 in
  let result:u8 = a +! b in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result

let another_panicfree_function (_: Prims.unit)
    : Prims.Pure Prims.unit
      Prims.l_True
      (ensures
        fun x ->
          let x:Prims.unit = x in
          false) =
  let not_much:i32 = mk_i32 0 in
  let nothing:i32 = mk_i32 0 in
  let still_not_much:i32 = not_much +! nothing in
  admit () (* Panic freedom *)
