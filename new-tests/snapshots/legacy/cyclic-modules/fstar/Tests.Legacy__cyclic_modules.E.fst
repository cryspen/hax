module Tests.Legacy__cyclic_modules.E
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_d {e1 as e1}
