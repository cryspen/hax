module New_tests.Legacy__cyclic_modules__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle {f as f}

include New_tests.Legacy__cyclic_modules__lib.Bundle {h as h}

include New_tests.Legacy__cyclic_modules__lib.Bundle {h2 as h2}
