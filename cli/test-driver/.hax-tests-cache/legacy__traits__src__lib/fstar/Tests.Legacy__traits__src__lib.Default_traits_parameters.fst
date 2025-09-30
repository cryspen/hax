module Tests.Legacy__traits__src__lib.Default_traits_parameters
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Bar (v_Self: Type0) (v_T: Type0) = { __marker_trait_t_Bar:Prims.unit }

class t_Foo (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_839825300468550254:t_Bar v_Self f_U;
  f_U:Type0
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Foo v_Self|} -> i._super_839825300468550254
