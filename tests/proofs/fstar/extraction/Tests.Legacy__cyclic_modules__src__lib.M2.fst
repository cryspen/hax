module Tests.Legacy__cyclic_modules__src__lib.M2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules__src__lib.Bundle_m1 {d as d}

include Tests.Legacy__cyclic_modules__src__lib.Bundle_m1 {b as b}

include Tests.Legacy__cyclic_modules__src__lib.Bundle_m1 {c as c}
