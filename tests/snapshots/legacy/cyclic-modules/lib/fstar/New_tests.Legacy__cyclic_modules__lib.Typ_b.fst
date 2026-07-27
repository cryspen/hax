module New_tests.Legacy__cyclic_modules__lib.Typ_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T1Rec as t_T1Rec}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {T1Rec_T1 as T1Rec_T1}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T2Rec as t_T2Rec}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {T2Rec_T2 as T2Rec_T2}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T1_cast_to_repr as t_T1_cast_to_repr}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T1 as t_T1}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {T1_T1 as T1_T1}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {t_T2 as t_T2}

include New_tests.Legacy__cyclic_modules__lib.Bundle_typ_a {T2_T2 as T2_T2}
