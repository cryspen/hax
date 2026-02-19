module New_tests.Rustc_coverage__auxiliary__inline_always_with_dead_code.Foo
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let called (_: Prims.unit) : Prims.unit = ()

let uncalled (_: Prims.unit) : Prims.unit = ()
