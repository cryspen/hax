module New_tests.Rustc_coverage__no_core
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let main (_: Prims.unit) : Prims.unit = ()
