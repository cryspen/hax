module Coverage.No_spans_if_not
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let affected_function (_: Prims.unit) : Prims.unit =
  if ~.false then () <: Prims.unit else () <: Prims.unit

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = affected_function () in
  ()
