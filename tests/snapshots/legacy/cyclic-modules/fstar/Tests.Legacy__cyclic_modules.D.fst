module Tests.Legacy__cyclic_modules.D
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_d {d1 as d1}

include Tests.Legacy__cyclic_modules.Bundle_d {d2 as d2}
