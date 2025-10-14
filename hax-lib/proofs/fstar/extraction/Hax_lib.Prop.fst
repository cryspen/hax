module Hax_lib.Prop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Hax_lib.Prop.Bundle {t_Prop as t_Prop}

include Hax_lib.Prop.Bundle {Prop as Prop}

include Hax_lib.Prop.Bundle {impl_7 as impl_7}

include Hax_lib.Prop.Bundle {impl_8 as impl_8}

include Hax_lib.Prop.Bundle {impl_9 as impl_9}

include Hax_lib.Prop.Bundle {impl__from_bool as impl_Prop__from_bool}

include Hax_lib.Prop.Bundle {impl__and as impl_Prop__and}

include Hax_lib.Prop.Bundle {impl__or as impl_Prop__or}

include Hax_lib.Prop.Bundle {impl__not as impl_Prop__not}

include Hax_lib.Prop.Bundle {impl__eq as impl_Prop__eq}

include Hax_lib.Prop.Bundle {impl__ne as impl_Prop__ne}

include Hax_lib.Prop.Bundle {impl__implies as impl_Prop__implies}

include Hax_lib.Prop.Bundle {impl_1 as impl_1}

include Hax_lib.Prop.Bundle {t_ToProp as t_ToProp}

include Hax_lib.Prop.Bundle {f_to_prop_pre as f_to_prop_pre}

include Hax_lib.Prop.Bundle {f_to_prop_post as f_to_prop_post}

include Hax_lib.Prop.Bundle {f_to_prop as f_to_prop}

include Hax_lib.Prop.Bundle {impl_2 as impl_ToProp_for_bool}

include Hax_lib.Prop.Bundle {impl_3 as impl_3}

include Hax_lib.Prop.Bundle {impl_4 as impl_4}

include Hax_lib.Prop.Bundle {impl_5 as impl_5}

include Hax_lib.Prop.Bundle {impl_6 as impl_6}

include Hax_lib.Prop.Bundle {v_forall as v_forall}

include Hax_lib.Prop.Bundle {v_exists as v_exists}

include Hax_lib.Prop.Bundle {implies as implies}
