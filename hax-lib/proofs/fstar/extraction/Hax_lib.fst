module Hax_lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Hax_lib.Bundle {v_assert as v_assert}

include Hax_lib.Bundle {assert_prop as assert_prop}

include Hax_lib.Bundle {v_assume as v_assume}

include Hax_lib.Bundle {v_inline as v_inline}

include Hax_lib.Bundle {inline_unsafe as inline_unsafe}

include Hax_lib.Bundle {any_to_unit as any_to_unit}

include Hax_lib.Bundle {e_internal_loop_invariant as e_internal_loop_invariant}

include Hax_lib.Bundle {e_internal_while_loop_invariant as e_internal_while_loop_invariant}

include Hax_lib.Bundle {e_internal_loop_decreases as e_internal_loop_decreases}

include Hax_lib.Bundle {t_Refinement as t_Refinement}

include Hax_lib.Bundle {t_RefineAs as t_RefineAs}

include Hax_lib.Bundle {f_into_checked_pre as f_into_checked_pre}

include Hax_lib.Bundle {f_into_checked_post as f_into_checked_post}

include Hax_lib.Bundle {f_into_checked as f_into_checked}
