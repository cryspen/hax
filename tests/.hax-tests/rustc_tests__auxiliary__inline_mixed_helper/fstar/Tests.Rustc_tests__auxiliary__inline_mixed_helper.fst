module Tests.Rustc_tests__auxiliary__inline_mixed_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inline_me (_: Prims.unit) : Prims.unit = ()

let no_inlining_please (_: Prims.unit) : Prims.unit = ()

let generic (#v_T: Type0) (_: Prims.unit) : Prims.unit = ()
