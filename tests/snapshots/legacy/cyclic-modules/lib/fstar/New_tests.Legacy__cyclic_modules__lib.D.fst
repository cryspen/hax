module New_tests.Legacy__cyclic_modules__lib.D
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_d {d1 as d1}

include New_tests.Legacy__cyclic_modules__lib.Bundle_d {d2 as d2}
