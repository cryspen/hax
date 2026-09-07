module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.B
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.Bundle {call_a as call_a}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.Second_example.Bundle {b as b}
