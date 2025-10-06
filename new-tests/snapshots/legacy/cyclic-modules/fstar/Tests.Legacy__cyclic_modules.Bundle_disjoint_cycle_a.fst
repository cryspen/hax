module Tests.Legacy__cyclic_modules.Bundle_disjoint_cycle_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let g (_: Prims.unit) : Prims.unit = ()

let h (_: Prims.unit) : Prims.unit = ()

let f (_: Prims.unit) : Prims.unit = h ()

let i (_: Prims.unit) : Prims.unit = g ()
