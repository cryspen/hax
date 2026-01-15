module Tests.Legacy__cyclic_modules.Rec1_same_name
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_rec1_same_name {f__from__rec1_same_name as f}
