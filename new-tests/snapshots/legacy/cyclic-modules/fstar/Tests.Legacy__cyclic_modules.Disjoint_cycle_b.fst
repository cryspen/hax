module Tests.Legacy__cyclic_modules.Disjoint_cycle_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_disjoint_cycle_a {h as h}

include Tests.Legacy__cyclic_modules.Bundle_disjoint_cycle_a {i as i}
