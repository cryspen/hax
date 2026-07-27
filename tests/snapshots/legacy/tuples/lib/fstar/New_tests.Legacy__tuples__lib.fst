module New_tests.Legacy__tuples__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): ssprove(HAX0001)
let project_tuple1 (_: Prims.unit) : u8 =
  let (tuple1: u8):u8 = mk_u8 3 <: u8 in
  tuple1
