module Coverage.Closure_unit_return
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let explicit_unit (_: Prims.unit) : Prims.unit =
  let closure: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let _:Prims.unit = () <: Prims.unit in
      ()
  in
  let _:Prims.unit = Core.Mem.drop closure in
  () <: Prims.unit

let implicit_unit (_: Prims.unit) : Prims.unit =
  let closure: Prims.unit -> Prims.unit =
    fun temp_0_ ->
      let _:Prims.unit = temp_0_ in
      let _:Prims.unit = () <: Prims.unit in
      ()
  in
  let _:Prims.unit = Core.Mem.drop closure in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = explicit_unit () in
  let _:Prims.unit = implicit_unit () in
  ()
