module Tests.Legacy__cyclic_modules.Disjoint_cycle_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_disjoint_cycle_a {f as f}

include Tests.Legacy__cyclic_modules.Bundle_disjoint_cycle_a {g as g}
