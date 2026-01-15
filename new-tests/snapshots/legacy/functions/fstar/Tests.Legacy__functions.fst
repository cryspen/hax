module Tests.Legacy__functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let calling_function_pointer__f (#v_T: Type0) (_: Prims.unit) : Prims.unit = ()

/// Issue #757
let calling_function_pointer (_: Prims.unit) : Prims.unit =
  let ff_ptr: Prims.unit -> Prims.unit = calling_function_pointer__f in
  let _:Prims.unit = calling_function_pointer__f #i32 () in
  ()
