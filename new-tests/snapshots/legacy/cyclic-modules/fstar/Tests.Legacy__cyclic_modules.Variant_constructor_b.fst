module Tests.Legacy__cyclic_modules.Variant_constructor_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {h as h}
