module Tests.Legacy__cyclic_modules.Enums_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_enums_a {t_U as t_U}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {U_A as U_A}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {U_B as U_B}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {U_C as U_C}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {t_T__from__enums_b as t_T}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_A as T_A}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_B as T_B}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {T_C as T_C}

include Tests.Legacy__cyclic_modules.Bundle_enums_a {f as f}
