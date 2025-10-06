module Tests.Legacy__cyclic_modules.Bundle_rec1_same_name
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rec f (x: i32) : i32 =
  if x >. mk_i32 0 then f__from__rec1_same_name (x -! mk_i32 1 <: i32) else mk_i32 0

and f__from__rec1_same_name (x: i32) : i32 = f x
