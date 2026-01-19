module New_tests.Legacy__cyclic_modules__lib.Enums_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {t_T as t_T}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_A__from__enums_a as T_A}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_B__from__enums_a as T_B}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_C__from__enums_a as T_C}

include New_tests.Legacy__cyclic_modules__lib.Bundle_enums_a {T_D as T_D}
