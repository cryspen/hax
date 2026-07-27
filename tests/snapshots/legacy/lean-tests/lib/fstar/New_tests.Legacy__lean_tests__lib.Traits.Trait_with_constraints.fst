module New_tests.Legacy__lean_tests__lib.Traits.Trait_with_constraints
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_T1 (v_Self: Type0) = { __marker_trait_t_T1:Prims.unit }

class t_T2 (v_Self: Type0) = {
  f_func_pre:{| i1: t_T1 v_Self |} -> v_Self -> Type0;
  f_func_post:{| i1: t_T1 v_Self |} -> v_Self -> bool -> Type0;
  f_func:{| i1: t_T1 v_Self |} -> x0: v_Self
    -> Prims.Pure bool (f_func_pre #i1 x0) (fun result -> f_func_post #i1 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_T1 v_A) : t_T2 v_A =
  {
    f_func_pre = (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_T1 v_A) (self: v_A) -> true);
    f_func_post
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_T1 v_A) (self: v_A) (out: bool) -> true);
    f_func = fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_T1 v_A) (self: v_A) -> true
  }
