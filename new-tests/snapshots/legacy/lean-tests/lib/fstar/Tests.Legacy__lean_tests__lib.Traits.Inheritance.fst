module Tests.Legacy__lean_tests__lib.Traits.Inheritance
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

class t_T3 (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_4681669453038871009:t_T2 v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_4145440524185414164:t_T1 v_Self;
  f_f3_pre:v_Self -> Type0;
  f_f3_post:v_Self -> usize -> Type0;
  f_f3:x0: v_Self -> Prims.Pure usize (f_f3_pre x0) (fun result -> f_f3_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_T3 v_Self|} -> i._super_4681669453038871009

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_T3 v_Self|} -> i._super_4145440524185414164

class t_Tp1 (v_Self: Type0) = {
  f_f1_pre:v_Self -> Type0;
  f_f1_post:v_Self -> usize -> Type0;
  f_f1:x0: v_Self -> Prims.Pure usize (f_f1_pre x0) (fun result -> f_f1_post x0 result)
}

class t_Tp2 (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_7003374932835866648:t_Tp1 v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15052774938804589053:t_T3 v_Self;
  f_fp2_pre:v_Self -> Type0;
  f_fp2_post:v_Self -> usize -> Type0;
  f_fp2:x0: v_Self -> Prims.Pure usize (f_fp2_pre x0) (fun result -> f_fp2_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Tp2 v_Self|} -> i._super_7003374932835866648

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Tp2 v_Self|} -> i._super_15052774938804589053

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 t_S =
  {
    f_f1_pre = (fun (self: t_S) -> true);
    f_f1_post = (fun (self: t_S) (out: usize) -> true);
    f_f1 = fun (self: t_S) -> mk_usize 1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T2_for_S: t_T2 t_S =
  {
    f_f2_pre = (fun (self: t_S) -> true);
    f_f2_post = (fun (self: t_S) (out: usize) -> true);
    f_f2 = fun (self: t_S) -> mk_usize 2
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T3_for_S: t_T3 t_S =
  {
    _super_4681669453038871009 = FStar.Tactics.Typeclasses.solve;
    _super_4145440524185414164 = FStar.Tactics.Typeclasses.solve;
    f_f3_pre = (fun (self: t_S) -> true);
    f_f3_post = (fun (self: t_S) (out: usize) -> true);
    f_f3 = fun (self: t_S) -> mk_usize 3
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Tp1_for_S: t_Tp1 t_S =
  {
    f_f1_pre = (fun (self: t_S) -> true);
    f_f1_post = (fun (self: t_S) (out: usize) -> true);
    f_f1 = fun (self: t_S) -> mk_usize 10
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Tp2_for_S: t_Tp2 t_S =
  {
    _super_7003374932835866648 = FStar.Tactics.Typeclasses.solve;
    _super_15052774938804589053 = FStar.Tactics.Typeclasses.solve;
    f_fp2_pre = (fun (self: t_S) -> true);
    f_fp2_post = (fun (self: t_S) (out: usize) -> true);
    f_fp2
    =
    fun (self: t_S) ->
      (((f_f1 #t_S #FStar.Tactics.Typeclasses.solve self <: usize) +!
          (f_f1 #t_S #FStar.Tactics.Typeclasses.solve self <: usize)
          <:
          usize) +!
        (f_f2 #t_S #FStar.Tactics.Typeclasses.solve self <: usize)
        <:
        usize) +!
      (f_f3 #t_S #FStar.Tactics.Typeclasses.solve self <: usize)
  }

let test (_: Prims.unit) : usize =
  let s:t_S = S <: t_S in
  (f_f3 #t_S #FStar.Tactics.Typeclasses.solve s <: usize) +! mk_usize 1
