module Tests.Legacy__cyclic_modules.Typ_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_TRec as t_TRec}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {TRec_T as TRec_T}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {TRec_Empty as TRec_Empty}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {t_T as t_T}

include Tests.Legacy__cyclic_modules.Bundle_typ_a {T_T as T_T}
