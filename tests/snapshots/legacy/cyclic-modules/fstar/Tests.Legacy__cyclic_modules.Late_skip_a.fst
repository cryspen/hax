module Tests.Legacy__cyclic_modules.Late_skip_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_late_skip_a {f__from__late_skip_a as f}
