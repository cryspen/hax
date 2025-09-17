module Core_models.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Fmt in
  ()

class t_Error (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_6821900375476161560:Core_models.Fmt.t_Display
  v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_14599973916339107634:Core_models.Fmt.t_Debug
  v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_6821900375476161560

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Error v_Self|} -> i._super_14599973916339107634
