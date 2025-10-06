module Tests.Legacy__cyclic_modules.Rec2_same_name
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_rec1_same_name {f as f}
