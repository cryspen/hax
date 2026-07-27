module New_tests.Legacy__lean_tests__lib.Structs.Base_expressions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_S = {
  f_f1:u32;
  f_f2:u32;
  f_f3:u32
}

let test (_: Prims.unit) : Prims.unit =
  let s1:t_S = { f_f1 = mk_u32 1; f_f2 = mk_u32 2; f_f3 = mk_u32 3 } <: t_S in
  let _:t_S = { s1 with f_f1 = mk_u32 0 } <: t_S in
  let _:t_S = { s1 with f_f2 = mk_u32 0 } <: t_S in
  let _:t_S = { s1 with f_f3 = mk_u32 0 } <: t_S in
  let _:t_S = { s1 with f_f1 = mk_u32 0; f_f2 = mk_u32 1 } <: t_S in
  let _:t_S = { s1 with f_f2 = mk_u32 0; f_f3 = mk_u32 1 } <: t_S in
  let _:t_S = { s1 with f_f3 = mk_u32 0; f_f1 = mk_u32 2 } <: t_S in
  let _:t_S = { s1 with f_f1 = mk_u32 0; f_f2 = mk_u32 1; f_f3 = mk_u32 0 } <: t_S in
  ()
