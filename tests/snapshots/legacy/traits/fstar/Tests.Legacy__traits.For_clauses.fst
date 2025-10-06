module Tests.Legacy__traits.For_clauses
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Foo (v_Self: Type0) (v_T: Type0) = {
  f_to_t_pre:v_Self -> Type0;
  f_to_t_post:v_Self -> v_T -> Type0;
  f_to_t:x0: v_Self -> Prims.Pure v_T (f_to_t_pre x0) (fun result -> f_to_t_post x0 result)
}

let e_f (#v_X: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Foo v_X u8) (x: v_X)
    : Prims.unit =
  let _:u8 = f_to_t #v_X #u8 #FStar.Tactics.Typeclasses.solve x in
  ()
