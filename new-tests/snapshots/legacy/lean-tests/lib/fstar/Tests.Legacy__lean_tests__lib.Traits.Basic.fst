module Tests.Legacy__lean_tests__lib.Traits.Basic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_T1 (v_Self: Type0) = {
  f_f1_pre:v_Self -> Type0;
  f_f1_post:v_Self -> usize -> Type0;
  f_f1:x0: v_Self -> Prims.Pure usize (f_f1_pre x0) (fun result -> f_f1_post x0 result);
  f_f2_pre:v_Self -> v_Self -> Type0;
  f_f2_post:v_Self -> v_Self -> usize -> Type0;
  f_f2:x0: v_Self -> x1: v_Self
    -> Prims.Pure usize (f_f2_pre x0 x1) (fun result -> f_f2_post x0 x1 result)
}

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 t_S =
  {
    f_f1_pre = (fun (self: t_S) -> true);
    f_f1_post = (fun (self: t_S) (out: usize) -> true);
    f_f1 = (fun (self: t_S) -> mk_usize 42);
    f_f2_pre = (fun (self: t_S) (other: t_S) -> true);
    f_f2_post = (fun (self: t_S) (other: t_S) (out: usize) -> true);
    f_f2 = fun (self: t_S) (other: t_S) -> mk_usize 43
  }

let f (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_T1 v_T) (x: v_T) : usize =
  (f_f1 #v_T #FStar.Tactics.Typeclasses.solve x <: usize) +!
  (f_f2 #v_T #FStar.Tactics.Typeclasses.solve x x <: usize)
