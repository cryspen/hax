module Core_models.Clone
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Clone (v_Self: Type0) = {
  f_clone_pre:v_Self -> Type0;
  f_clone_post:v_Self -> v_Self -> Type0;
  f_clone:x0: v_Self -> Prims.Pure v_Self (f_clone_pre x0) (fun result -> f_clone_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Clone v_T =
  {
    f_clone_pre = (fun (self: v_T) -> true);
    f_clone_post = (fun (self: v_T) (out: v_T) -> true);
    f_clone = fun (self: v_T) -> self
  }
