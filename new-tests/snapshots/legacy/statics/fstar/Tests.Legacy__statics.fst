module Tests.Legacy__statics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_FOO: usize = mk_usize 0

let get_foo (_: Prims.unit) : usize = v_FOO
