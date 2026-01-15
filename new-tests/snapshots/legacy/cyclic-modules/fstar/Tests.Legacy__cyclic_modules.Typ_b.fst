module Tests.Legacy__cyclic_modules.Typ_b
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T1Rec as t_T1Rec}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {T1Rec_T1 as T1Rec_T1}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T2Rec as t_T2Rec}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {T2Rec_T2 as T2Rec_T2}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T1_cast_to_repr as t_T1_cast_to_repr}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T1 as t_T1}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {T1_T1 as T1_T1}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T2 as t_T2}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {T2_T2 as T2_T2}
