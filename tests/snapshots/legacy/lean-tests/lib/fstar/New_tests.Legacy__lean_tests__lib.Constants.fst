module New_tests.Legacy__lean_tests__lib.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let v_C1: u32 = mk_u32 5678

let v_C2: u32 = v_C1 +! mk_u32 1

let v_C3: u32 = if true then mk_u32 890 else mk_u32 9 /! mk_u32 0

let computation (x: u32) : u32 = (x +! x <: u32) +! mk_u32 1

let v_C4: u32 = (computation v_C1 <: u32) +! v_C2

let test (_: Prims.unit) : Prims.unit =
  let x:u32 = v_C1 +! mk_u32 1 in
  let y:u32 = v_C2 +! v_C3 in
  let z:u32 = v_C4 -! v_C3 in
  ()
