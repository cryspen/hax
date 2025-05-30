module Coverage.Test_harness
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let unused (_: Prims.unit) : Prims.unit = ()
