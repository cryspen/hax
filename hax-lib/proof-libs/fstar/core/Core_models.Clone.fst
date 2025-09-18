module Core_models.Clone
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Clone v_T =
  {
    f_clone_pre = (fun (self: v_T) -> true);
    f_clone_post = (fun (self: v_T) (out: v_T) -> true);
    f_clone = fun (self: v_T) -> self
  }
