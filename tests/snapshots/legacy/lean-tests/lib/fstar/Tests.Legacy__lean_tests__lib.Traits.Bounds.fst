module Tests.Legacy__lean_tests__lib.Traits.Bounds
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_T1 (v_Self: Type0) = {
  f_f1_pre:v_Self -> Type0;
  f_f1_post:v_Self -> usize -> Type0;
  f_f1:x0: v_Self -> Prims.Pure usize (f_f1_pre x0) (fun result -> f_f1_post x0 result)
}

class t_T2 (v_Self: Type0) = {
  f_f2_pre:v_Self -> Type0;
  f_f2_post:v_Self -> usize -> Type0;
  f_f2:x0: v_Self -> Prims.Pure usize (f_f2_pre x0) (fun result -> f_f2_post x0 result)
}

class t_Test (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1529261179564284687:t_T2 v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_5255745353837564140:t_T1 v_T;
  f_ff_test_pre:v_Self -> v_T -> Type0;
  f_ff_test_post:v_Self -> v_T -> usize -> Type0;
  f_ff_test:x0: v_Self -> x1: v_T
    -> Prims.Pure usize (f_ff_test_pre x0 x1) (fun result -> f_ff_test_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_Test v_Self v_T|} -> i._super_1529261179564284687

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_Test v_Self v_T|} -> i._super_5255745353837564140

type t_S1 = | S1 : t_S1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 t_S1 =
  {
    f_f1_pre = (fun (self: t_S1) -> true);
    f_f1_post = (fun (self: t_S1) (out: usize) -> true);
    f_f1 = fun (self: t_S1) -> mk_usize 0
  }

type t_S2 = | S2 : t_S2

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T2_for_S2: t_T2 t_S2 =
  {
    f_f2_pre = (fun (self: t_S2) -> true);
    f_f2_post = (fun (self: t_S2) (out: usize) -> true);
    f_f2 = fun (self: t_S2) -> mk_usize 1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_Test t_S2 t_S1 =
  {
    _super_1529261179564284687 = FStar.Tactics.Typeclasses.solve;
    f_ff_test_pre = (fun (self: t_S2) (x: t_S1) -> true);
    f_ff_test_post = (fun (self: t_S2) (x: t_S1) (out: usize) -> true);
    f_ff_test
    =
    fun (self: t_S2) (x: t_S1) ->
      ((f_f1 #t_S1 #FStar.Tactics.Typeclasses.solve x <: usize) +!
        (f_f2 #t_S2 #FStar.Tactics.Typeclasses.solve self <: usize)
        <:
        usize) +!
      mk_usize 1
  }

let test (x1: t_S1) (x2: t_S2) : usize =
  (f_ff_test #t_S2 #t_S1 #FStar.Tactics.Typeclasses.solve x2 x1 <: usize) +!
  (f_f1 #t_S1 #FStar.Tactics.Typeclasses.solve x1 <: usize)
