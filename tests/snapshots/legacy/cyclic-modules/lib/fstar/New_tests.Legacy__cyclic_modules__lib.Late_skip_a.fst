module New_tests.Legacy__cyclic_modules__lib.Late_skip_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_late_skip_a {f__from__late_skip_a as f}
