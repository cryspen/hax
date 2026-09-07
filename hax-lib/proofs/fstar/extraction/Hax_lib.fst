module Hax_lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Tactics

val v_assert (p: bool) : Pure unit (requires p) (ensures (fun x -> p))
let v_assert (v__formula: bool) = ()

val assert_prop (p: prop) : Pure unit (requires p) (ensures (fun x -> p))
let assert_prop (v__formula: prop) = ()

val v_assume (p: prop) : Pure unit (requires True) (ensures (fun x -> p))
let v_assume (v__formula: prop) = assume v__formula
