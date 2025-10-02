module Tests.Rustc_tests__no_core
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Prims.unit = ()
