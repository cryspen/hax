module Tests.Legacy__cyclic_modules__src__lib.Rec1_same_name
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules__src__lib.Bundle_rec1_same_name {f__from__rec1_same_name as f}
