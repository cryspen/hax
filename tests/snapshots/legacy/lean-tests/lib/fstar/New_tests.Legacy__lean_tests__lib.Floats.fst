module New_tests.Legacy__lean_tests__lib.Floats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): ssprove(HAX0001)
let v_N: float = mk_float "1.0"

/// @fail(extraction): ssprove(HAX0001)
let test (_: Prims.unit) : Prims.unit =
  let l0:float = mk_float "1.0" in
  let l1:float = mk_float "0.9" in
  let l2:float = mk_float "5.0" in
  let l5:float = v_N in
  ()

/// @fail(extraction): ssprove(HAX0001)
let f (x y: float) : float = y
