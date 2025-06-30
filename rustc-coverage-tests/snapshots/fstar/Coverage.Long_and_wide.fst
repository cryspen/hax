module Coverage.Long_and_wide
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let wide_function (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = () <: Prims.unit in
  ()

let long_function (_: Prims.unit) : Prims.unit = ()

let far_function (_: Prims.unit) : Prims.unit = ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = wide_function () in
  let _:Prims.unit = long_function () in
  let _:Prims.unit = far_function () in
  ()
