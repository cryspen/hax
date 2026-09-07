module New_tests.Legacy__cyclic_modules__lib.Disjoint_cycle_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_disjoint_cycle_a {f as f}

include New_tests.Legacy__cyclic_modules__lib.Bundle_disjoint_cycle_a {g as g}
