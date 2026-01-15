module Tests.Legacy__lean_tests__lib.Structs.Miscellaneous
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_S = { f_f:i32 }

let test_tuples (_: Prims.unit) : (i32 & i32) =
  let lit:i32 = mk_i32 1 in
  let constr:t_S = { f_f = mk_i32 42 } <: t_S in
  let proj:i32 = constr.f_f in
  let ite:(i32 & i32) =
    if true
    then mk_i32 1, mk_i32 2 <: (i32 & i32)
    else
      let z:i32 = mk_i32 1 +! mk_i32 2 in
      z, z <: (i32 & i32)
  in
  mk_i32 1, mk_i32 2 <: (i32 & i32)
