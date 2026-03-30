module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.B
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {t_B as t_B}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {B as B}

include New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle {impl__mka as impl_B__mka}
