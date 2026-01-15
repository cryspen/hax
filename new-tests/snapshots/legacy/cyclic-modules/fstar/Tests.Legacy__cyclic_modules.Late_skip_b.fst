module Tests.Legacy__cyclic_modules.Late_skip_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_late_skip_a {f as f}
