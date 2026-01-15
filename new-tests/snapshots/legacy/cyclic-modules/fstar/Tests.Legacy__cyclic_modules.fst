module Tests.Legacy__cyclic_modules
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle {f as f}

include Tests.Legacy__cyclic_modules.Bundle {h as h}

include Tests.Legacy__cyclic_modules.Bundle {h2 as h2}
