module New_tests.Legacy__reconstruct_asserts_else__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Value in the else branch.
let checked_incr (c: bool) (x: u32) : u32 =
  let _:Prims.unit = Hax_lib.v_assert (~.c <: bool) in
  x +! mk_u32 1

/// Nested panic-elses.
let nested (c d: bool) (x: u32) : u32 =
  let _:Prims.unit = Hax_lib.v_assert (~.c <: bool) in
  let _:Prims.unit = Hax_lib.v_assert (~.d <: bool) in
  x

/// No else.
let bare (c: bool) : Prims.unit = Hax_lib.v_assert (~.c <: bool)
