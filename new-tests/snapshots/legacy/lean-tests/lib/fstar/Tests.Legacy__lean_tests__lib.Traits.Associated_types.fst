module Tests.Legacy__lean_tests__lib.Traits.Associated_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Foo (v_Self: Type0) (v_T: Type0) = { __marker_trait_t_Foo:Prims.unit }

class t_Bar (v_Self: Type0) = { __marker_trait_t_Bar:Prims.unit }

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Bar_for_i16: t_Bar i16 = { __marker_trait_t_Bar = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_A: Type0) : t_Foo (u32 & v_A) i16 = { __marker_trait_t_Foo = () }

class t_T1 (v_Self: Type0) = {
  f_T:Type0;
  f_f_pre:v_Self -> f_T -> Type0;
  f_f_post:v_Self -> f_T -> f_T -> Type0;
  f_f:x0: v_Self -> x1: f_T -> Prims.Pure f_T (f_f_pre x0 x1) (fun result -> f_f_post x0 x1 result)
}

class t_T3 (v_Self: Type0) = {
  f_T:Type0;
  f_T_i0:t_Bar f_T;
  f_Tp:Type0;
  f_Tp_i0:t_Foo f_Tp f_T;
  f_f_pre:#v_A: Type0 -> {| i0: t_Bar v_A |} -> v_Self -> f_T -> f_Tp -> Type0;
  f_f_post:#v_A: Type0 -> {| i0: t_Bar v_A |} -> v_Self -> f_T -> f_Tp -> usize -> Type0;
  f_f:#v_A: Type0 -> {| i0: t_Bar v_A |} -> x0: v_Self -> x1: f_T -> x2: f_Tp
    -> Prims.Pure usize
        (f_f_pre #v_A #i0 x0 x1 x2)
        (fun result -> f_f_post #v_A #i0 x0 x1 x2 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 t_S =
  {
    f_T = i32;
    f_f_pre = (fun (self: t_S) (x: i32) -> true);
    f_f_post = (fun (self: t_S) (x: i32) (out: i32) -> true);
    f_f = fun (self: t_S) (x: i32) -> mk_i32 2121
  }

class t_T2 (v_Self: Type0) = {
  f_T:Type0;
  f_T_i0:t_T1 f_T;
  f_f_pre:v_Self -> f_T -> Type0;
  f_f_post:v_Self -> f_T -> usize -> Type0;
  f_f:x0: v_Self -> x1: f_T
    -> Prims.Pure usize (f_f_pre x0 x1) (fun result -> f_f_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T2_for_S: t_T2 t_S =
  {
    f_T = t_S;
    f_T_i0 = FStar.Tactics.Typeclasses.solve;
    f_f_pre = (fun (self: t_S) (x: t_S) -> true);
    f_f_post = (fun (self: t_S) (x: t_S) (out: usize) -> true);
    f_f = fun (self: t_S) (x: t_S) -> mk_usize 21
  }
