module Tests.Legacy__reordering.Mut_rec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rec g (_: Prims.unit) : Prims.unit = f ()

and f (_: Prims.unit) : Prims.unit = g ()

let ff_2_ (_: Prims.unit) : Prims.unit = f ()
