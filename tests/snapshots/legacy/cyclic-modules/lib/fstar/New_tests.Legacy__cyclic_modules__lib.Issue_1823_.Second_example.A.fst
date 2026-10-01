module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.A
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.Bundle {call_b as call_b}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.Bundle {a as a}
