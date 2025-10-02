module Tests.Rustc_tests__auxiliary__discard_all_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let external_function (_: Prims.unit) : Prims.unit = ()
