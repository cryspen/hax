module Tests.Legacy__cyclic_modules.Enums_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_enums_a {t_T as t_T}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_A__from__enums_a as T_A}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_B__from__enums_a as T_B}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_C__from__enums_a as T_C}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_D as T_D}
