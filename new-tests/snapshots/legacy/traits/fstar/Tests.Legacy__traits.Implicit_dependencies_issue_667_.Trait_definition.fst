module Tests.Legacy__traits.Implicit_dependencies_issue_667_.Trait_definition
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_MyTrait (v_Self: Type0) = {
  f_my_method_pre:v_Self -> Type0;
  f_my_method_post:v_Self -> Prims.unit -> Type0;
  f_my_method:x0: v_Self
    -> Prims.Pure Prims.unit (f_my_method_pre x0) (fun result -> f_my_method_post x0 result)
}
