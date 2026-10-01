module New_tests.Legacy__cyclic_modules__lib.Disjoint_cycle_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_disjoint_cycle_a {h as h}

include New_tests.Legacy__cyclic_modules__lib.Bundle_disjoint_cycle_a {i as i}
