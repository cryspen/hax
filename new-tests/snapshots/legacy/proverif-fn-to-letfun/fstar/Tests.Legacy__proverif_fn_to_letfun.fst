module Tests.Legacy__proverif_fn_to_letfun
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_A = {
  f_x:usize;
  f_y:u8
}

type t_B = { f_b:bool }

let some_function (_: Prims.unit) : bool = true

let some_other_function (b: bool) : u8 = mk_u8 5

let longer_function (x: string) : t_A =
  let b:bool = some_function () in
  let d:u8 = some_other_function b in
  { f_x = mk_usize 12; f_y = mk_u8 9 } <: t_A

let another_longer_function (_: Prims.unit) : t_B =
  let b:bool = some_function () in
  let d:u8 = some_other_function b in
  { f_b = false } <: t_B

let void_function (_: Prims.unit) : Prims.unit =
  let b:bool = some_function () in
  let d:u8 = some_other_function b in
  ()
