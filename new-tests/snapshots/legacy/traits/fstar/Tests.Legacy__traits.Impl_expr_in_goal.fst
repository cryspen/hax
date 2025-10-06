module Tests.Legacy__traits.Impl_expr_in_goal
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_T1 (v_Self: Type0) = { f_Assoc:Type0 }

class t_T2 (v_Self: Type0) = { __marker_trait_t_T2:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_T1 v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_T2 i0.f_Assoc)
    : t_T2 v_U = { __marker_trait_t_T2 = () }
