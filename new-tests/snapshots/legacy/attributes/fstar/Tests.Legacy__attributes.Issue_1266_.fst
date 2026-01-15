module Tests.Legacy__attributes.Issue_1266_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_T (v_Self: Type0) = {
  f_v_pre:v_Self -> Type0;
  f_v_post:x: v_Self -> x_future: v_Self -> pred: Type0{pred ==> true};
  f_v:x0: v_Self -> Prims.Pure v_Self (f_v_pre x0) (fun result -> f_v_post x0 result)
}
