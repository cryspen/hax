module Tests.Legacy__lean_tests__lib.Ite
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let test1 (_: Prims.unit) : i32 =
  let x:i32 = if true then mk_i32 0 else mk_i32 1 in
  if false then mk_i32 2 else mk_i32 3

let test2 (b: bool) : i32 =
  let x:i32 = if b then mk_i32 0 else mk_i32 9 in
  let y:i32 = mk_i32 0 in
  let y:i32 = if true then (y +! x <: i32) +! mk_i32 1 else (y -! x <: i32) -! mk_i32 1 in
  if b
  then
    let z:i32 = y +! y in
    (z +! y <: i32) +! x
  else
    let z:i32 = y -! x in
    (z +! y <: i32) +! x
