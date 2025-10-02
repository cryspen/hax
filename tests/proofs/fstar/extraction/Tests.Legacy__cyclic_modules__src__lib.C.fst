module Tests.Legacy__cyclic_modules__src__lib.C
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let i (_: Prims.unit) : Prims.unit = ()
