module New_tests.Legacy__traits__lib.For_clauses.Issue_495_.Minimized_3_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Trait (v_Self: Type0) = { __marker_trait_t_Trait:Prims.unit }

/// @fail(extraction): legacy-lean(HAX0001)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnMut v_P u8)
    : t_Trait v_P = { __marker_trait_t_Trait = () }
