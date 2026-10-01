module New_tests.Legacy__cyclic_modules__lib.C
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let i (_: Prims.unit) : Prims.unit = ()
