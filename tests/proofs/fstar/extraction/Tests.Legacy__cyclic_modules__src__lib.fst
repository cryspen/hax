module Tests.Legacy__cyclic_modules__src__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules__src__lib.Bundle {f as f}

include Tests.Legacy__cyclic_modules__src__lib.Bundle {h as h}

include Tests.Legacy__cyclic_modules__src__lib.Bundle {h2 as h2}
