module Tests.Legacy__assert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let asserts (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = Hax_lib.v_assert true in
  let _:Prims.unit = Hax_lib.v_assert (mk_i32 1 =. mk_i32 1 <: bool) in
  let _:Prims.unit =
    match mk_i32 2, mk_i32 2 <: (i32 & i32) with
    | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
  in
  let _:Prims.unit =
    match mk_i32 1, mk_i32 2 <: (i32 & i32) with
    | left_val, right_val -> Hax_lib.v_assert (~.(left_val =. right_val <: bool) <: bool)
  in
  ()
