module Tests.Legacy__cyclic_modules.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let f (_: Prims.unit) : Prims.unit = ()

let h2 (_: Prims.unit) : Prims.unit = Tests.Legacy__cyclic_modules.C.i ()

let g (_: Prims.unit) : Prims.unit = f ()

let h (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = g () in
  Tests.Legacy__cyclic_modules.C.i ()
