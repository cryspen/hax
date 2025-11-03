module Coverage.Mcdc.Inlined_expressions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let inlined_instance (a b: bool) : bool = a && b

let main (_: Prims.unit) : Prims.unit =
  let _:bool = inlined_instance true false in
  let _:bool = inlined_instance false true in
  let _:bool = inlined_instance true true in
  ()
