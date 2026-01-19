module New_tests.Legacy__cyclic_modules__lib.M2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_m1 {d as d}

include New_tests.Legacy__cyclic_modules__lib.Bundle_m1 {b as b}

include New_tests.Legacy__cyclic_modules__lib.Bundle_m1 {c as c}
