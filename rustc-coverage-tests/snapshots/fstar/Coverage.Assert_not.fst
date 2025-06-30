module Coverage.Assert_not
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = Hax_lib.v_assert true in
  let _:Prims.unit = Hax_lib.v_assert (~.false <: bool) in
  let _:Prims.unit = Hax_lib.v_assert (~.(~.true <: bool) <: bool) in
  let _:Prims.unit = Hax_lib.v_assert (~.(~.(~.false <: bool) <: bool) <: bool) in
  ()
