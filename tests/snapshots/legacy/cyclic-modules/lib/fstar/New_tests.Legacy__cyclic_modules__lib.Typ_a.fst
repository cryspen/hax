module New_tests.Legacy__cyclic_modules__lib.Typ_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_TRec as t_TRec}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {TRec_T as TRec_T}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {TRec_Empty as TRec_Empty}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T as t_T}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {T_T as T_T}
