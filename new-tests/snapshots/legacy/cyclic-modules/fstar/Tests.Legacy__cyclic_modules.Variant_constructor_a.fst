module Tests.Legacy__cyclic_modules.Variant_constructor_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {t_Context as t_Context}

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {Context_A as Context_A}

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {Context_B as Context_B}

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {f as f}

include Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a {impl__test as impl_Context__test}
