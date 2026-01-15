module Tests.Legacy__traits.Interlaced_consts_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Bar (v_FooConst: usize) (v_FooType: Type0) =
  | Bar : t_Array v_FooType v_FooConst -> t_Bar v_FooConst v_FooType

class t_Foo (v_Self: Type0) (v_FooConst: usize) (v_FooType: Type0) = {
  f_fun_pre:
      v_FunConst: usize ->
      #v_FunType: Type0 ->
      t_Array v_FooType v_FooConst ->
      t_Array v_FunType v_FunConst
    -> Type0;
  f_fun_post:
      v_FunConst: usize ->
      #v_FunType: Type0 ->
      t_Array v_FooType v_FooConst ->
      t_Array v_FunType v_FunConst ->
      Prims.unit
    -> Type0;
  f_fun:
      v_FunConst: usize ->
      #v_FunType: Type0 ->
      x0: t_Array v_FooType v_FooConst ->
      x1: t_Array v_FunType v_FunConst
    -> Prims.Pure Prims.unit
        (f_fun_pre v_FunConst #v_FunType x0 x1)
        (fun result -> f_fun_post v_FunConst #v_FunType x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_FooConst: usize) (#v_FooType #v_SelfType: Type0) : t_Foo v_SelfType v_FooConst v_FooType =
  {
    f_fun_pre
    =
    (fun
        (v_FunConst: usize)
        (#v_FunType: Type0)
        (x: t_Array v_FooType v_FooConst)
        (y: t_Array v_FunType v_FunConst)
        ->
        true);
    f_fun_post
    =
    (fun
        (v_FunConst: usize)
        (#v_FunType: Type0)
        (x: t_Array v_FooType v_FooConst)
        (y: t_Array v_FunType v_FunConst)
        (out: Prims.unit)
        ->
        true);
    f_fun
    =
    fun
      (v_FunConst: usize)
      (#v_FunType: Type0)
      (x: t_Array v_FooType v_FooConst)
      (y: t_Array v_FunType v_FunConst)
      ->
      ()
  }
