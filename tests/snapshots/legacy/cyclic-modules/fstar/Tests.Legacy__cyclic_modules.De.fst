module Tests.Legacy__cyclic_modules.De
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_d {de1 as de1}
