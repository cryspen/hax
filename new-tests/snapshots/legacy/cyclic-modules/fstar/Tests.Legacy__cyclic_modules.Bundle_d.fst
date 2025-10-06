module Tests.Legacy__cyclic_modules.Bundle_d
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let d1 (_: Prims.unit) : Prims.unit = ()

let e1 (_: Prims.unit) : Prims.unit = d1 ()

let de1 (_: Prims.unit) : Prims.unit = e1 ()

let d2 (_: Prims.unit) : Prims.unit = de1 ()
