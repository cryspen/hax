module New_tests.Legacy__lean_tests__lib.Monadic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_S = { f_f:u32 }

let test (_: Prims.unit) : Prims.unit =
  let _:i32 = mk_i32 9 in
  let _:i32 = mk_i32 9 +! mk_i32 9 in
  let _:t_S = { f_f = mk_u32 9 } <: t_S in
  let _:t_S = { f_f = mk_u32 9 +! mk_u32 9 } <: t_S in
  let _:u32 = ({ f_f = mk_u32 9 +! mk_u32 9 } <: t_S).f_f in
  let _:u32 = ({ f_f = mk_u32 9 +! mk_u32 9 <: u32 } <: t_S).f_f +! mk_u32 9 in
  let _:i32 = if true then mk_i32 3 +! mk_i32 4 else mk_i32 3 -! mk_i32 4 in
  let _:i32 =
    if (mk_i32 9 +! mk_i32 9 <: i32) =. mk_i32 0 then mk_i32 3 +! mk_i32 4 else mk_i32 3 -! mk_i32 4
  in
  let _:Prims.unit =
    if true
    then
      let x:i32 = mk_i32 9 in
      let _:i32 = mk_i32 3 +! x in
      ()
    else
      let y:i32 = mk_i32 19 in
      let _:i32 = (mk_i32 3 +! y <: i32) -! mk_i32 4 in
      ()
  in
  ()
