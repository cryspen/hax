module New_tests.Legacy__lean_tests__lib.Associated_types.Multiple_projections
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_FnOnce (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0
}

let func
      (#v_T #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_FnOnce v_D v_T)
      (#_: unit{i0.f_Output == v_U})
      (#_: unit{i1.f_Output == v_U})
      (d: v_D)
      (f: v_F)
      (u: v_U)
    : Prims.unit = ()
