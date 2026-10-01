module New_tests.Legacy__cyclic_modules__lib.E
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_d {e1 as e1}
