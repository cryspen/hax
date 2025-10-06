module Tests.Legacy__cyclic_modules.Bundle_m1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let d (_: Prims.unit) : Prims.unit = ()

let c (_: Prims.unit) : Prims.unit = ()

let a (_: Prims.unit) : Prims.unit = c ()

let b (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = a () in
  d ()
