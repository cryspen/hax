module New_tests.Legacy__traits__lib.Gat_bounds_issue_1907_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

class t_Bound (v_Self: Type0) = { __marker_trait_t_Bound:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Bound u8 = { __marker_trait_t_Bound = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Bound v_A)
    : t_Bound (u8 & v_A) = { __marker_trait_t_Bound = () }

type t_S = | S : t_S

class t_WithGat (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Assoc:Type0;
  f_Assoc_i0:t_Bound f_Assoc
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_WithGat_for_S: t_WithGat t_S =
  { f_Assoc = (u8 & v_A); f_Assoc_i0 = FStar.Tactics.Typeclasses.solve }
