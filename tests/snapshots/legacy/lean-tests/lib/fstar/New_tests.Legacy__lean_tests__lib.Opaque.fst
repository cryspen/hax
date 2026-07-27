module New_tests.Legacy__lean_tests__lib.Opaque
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

assume
val an_opaque_fn': Prims.unit -> Prims.unit

unfold
let an_opaque_fn = an_opaque_fn'
