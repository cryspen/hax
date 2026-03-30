module New_tests.Legacy__traits__lib.Recursive_trait_with_assoc_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Trait1 (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_T:Type0;
  f_T_i0:t_Trait1 f_T
}

class t_Trait2 (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Trait1 v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_U:Type0
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Trait2 v_Self|} -> i._super_i0
