module Tests.Legacy__attributes.Int_model
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

unfold type t_Int = int

let impl_2: Core_models.Clone.t_Clone t_Int =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_Copy t_Int

unfold
let impl_1 = impl_1'

unfold let add x y = x + y

unfold instance impl: Core.Ops.Arith.t_Sub t_Int t_Int =
  {
    f_Output = t_Int;
    f_sub_pre = (fun (self: t_Int) (other: t_Int) -> true);
    f_sub_post = (fun (self: t_Int) (other: t_Int) (out: t_Int) -> true);
    f_sub = fun (self: t_Int) (other: t_Int) -> self + other
  }
