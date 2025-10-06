module Tests.Legacy__cyclic_modules.E
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_d {e1 as e1}
