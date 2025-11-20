module Core_models.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Error (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Fmt.t_Display v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:Core_models.Fmt.t_Debug v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_i1
