module New_tests.Rustc_coverage__auxiliary__inline_mixed_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let inline_me (_: Prims.unit) : Prims.unit = ()

let no_inlining_please (_: Prims.unit) : Prims.unit = ()

let generic (#v_T: Type0) (_: Prims.unit) : Prims.unit = ()
