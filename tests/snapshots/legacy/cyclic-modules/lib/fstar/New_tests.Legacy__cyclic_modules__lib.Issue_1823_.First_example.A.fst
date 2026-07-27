module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.A
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {t_A as t_A}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {A as A}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {impl__mkb as impl_A__mkb}
