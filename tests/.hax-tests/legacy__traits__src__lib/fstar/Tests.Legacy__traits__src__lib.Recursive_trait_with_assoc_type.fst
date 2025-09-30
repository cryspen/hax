module Tests.Legacy__traits__src__lib.Recursive_trait_with_assoc_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Trait1 (v_Self: Type0) = {
  f_T:Type0;
  f_T_17162696321787740620:t_Trait1 f_T
}

class t_Trait2 (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_14865019862078329014:t_Trait1 v_Self;
  f_U:Type0
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Trait2 v_Self|} -> i._super_14865019862078329014
