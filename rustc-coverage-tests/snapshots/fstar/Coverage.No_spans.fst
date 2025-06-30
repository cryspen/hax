module Coverage.No_spans
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let affected_function (_: Prims.unit) :  Prims.unit -> Prims.unit =
  fun temp_0_ ->
    let _:Prims.unit = temp_0_ in
    () <: Prims.unit

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    Core.Ops.Function.f_call #_
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      (affected_function () <: _)
      (() <: Prims.unit)
  in
  ()
