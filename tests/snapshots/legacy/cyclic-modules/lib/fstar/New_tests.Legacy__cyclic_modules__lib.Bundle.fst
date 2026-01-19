module New_tests.Legacy__cyclic_modules__lib.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let f (_: Prims.unit) : Prims.unit = ()

let h2 (_: Prims.unit) : Prims.unit = New_tests.Legacy__cyclic_modules__lib.C.i ()

let g (_: Prims.unit) : Prims.unit = f ()

let h (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = g () in
  New_tests.Legacy__cyclic_modules__lib.C.i ()
