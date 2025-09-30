module Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let called (_: Prims.unit) : Prims.unit = ()

let uncalled (_: Prims.unit) : Prims.unit = ()
