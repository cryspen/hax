module Tests.Legacy__reordering.Independent_cycles
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let rec c (_: Prims.unit) : Prims.unit = a ()

and a (_: Prims.unit) : Prims.unit = c ()

let rec d (_: Prims.unit) : Prims.unit = b ()

and b (_: Prims.unit) : Prims.unit = d ()
