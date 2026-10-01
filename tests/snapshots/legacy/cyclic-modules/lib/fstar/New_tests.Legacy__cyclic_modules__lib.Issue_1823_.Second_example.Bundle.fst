module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let a (_: Prims.unit) : Prims.unit = ()

let call_a (_: Prims.unit) : Prims.unit = a ()

let b (_: Prims.unit) : Prims.unit = ()

let call_b (_: Prims.unit) : Prims.unit = b ()
