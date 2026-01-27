module Hax_lib.Prop.Constructors
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Hax_lib.Prop.Bundle {from_bool as from_bool}

include Hax_lib.Prop.Bundle {v_and as v_and}

include Hax_lib.Prop.Bundle {or as or}

include Hax_lib.Prop.Bundle {not as not}

include Hax_lib.Prop.Bundle {eq as eq}

include Hax_lib.Prop.Bundle {ne as ne}

include Hax_lib.Prop.Bundle {implies__from__constructors as implies}

include Hax_lib.Prop.Bundle {v_forall__from__constructors as v_forall}

include Hax_lib.Prop.Bundle {v_exists__from__constructors as v_exists}
