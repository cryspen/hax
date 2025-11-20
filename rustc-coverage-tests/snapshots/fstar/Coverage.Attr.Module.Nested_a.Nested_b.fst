module Coverage.Attr.Module.Nested_a.Nested_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let inner (_: Prims.unit) : Prims.unit = ()
