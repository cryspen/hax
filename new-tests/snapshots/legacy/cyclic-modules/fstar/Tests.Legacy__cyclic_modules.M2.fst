module Tests.Legacy__cyclic_modules.M2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_m1 {d as d}

include Tests.Legacy__cyclic_modules.Bundle_m1 {b as b}

include Tests.Legacy__cyclic_modules.Bundle_m1 {c as c}
