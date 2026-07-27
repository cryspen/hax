module New_tests.Legacy__cyclic_modules__lib.Enums_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {t_U as t_U}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {U_A as U_A}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {U_B as U_B}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {U_C as U_C}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {t_T__from__enums_b as t_T}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_A as T_A}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_B as T_B}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_C as T_C}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {f as f}
