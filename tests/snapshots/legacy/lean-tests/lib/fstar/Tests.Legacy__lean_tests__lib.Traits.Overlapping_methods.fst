module Tests.Legacy__lean_tests__lib.Traits.Overlapping_methods
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_T1 (v_Self: Type0) = {
  f_f_pre:v_Self -> Type0;
  f_f_post:v_Self -> usize -> Type0;
  f_f:x0: v_Self -> Prims.Pure usize (f_f_pre x0) (fun result -> f_f_post x0 result)
}

class t_T2 (v_Self: Type0) = {
  f_f_pre:v_Self -> Type0;
  f_f_post:v_Self -> usize -> Type0;
  f_f:x0: v_Self -> Prims.Pure usize (f_f_pre x0) (fun result -> f_f_post x0 result)
}

class t_T3 (v_Self: Type0) = {
  f_f_pre:v_Self -> Type0;
  f_f_post:v_Self -> usize -> Type0;
  f_f:x0: v_Self -> Prims.Pure usize (f_f_pre x0) (fun result -> f_f_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 u32 =
  {
    f_f_pre = (fun (self: u32) -> true);
    f_f_post = (fun (self: u32) (out: usize) -> true);
    f_f = fun (self: u32) -> mk_usize 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T2_for_u32: t_T2 u32 =
  {
    f_f_pre = (fun (self: u32) -> true);
    f_f_post = (fun (self: u32) (out: usize) -> true);
    f_f = fun (self: u32) -> mk_usize 1
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_T3_for_u32: t_T3 u32 =
  {
    f_f_pre = (fun (self: u32) -> true);
    f_f_post = (fun (self: u32) (out: usize) -> true);
    f_f = fun (self: u32) -> mk_usize 2
  }

let test (_: Prims.unit) : usize =
  let (x: u32):u32 = mk_u32 9 in
  ((f_f #u32 #FStar.Tactics.Typeclasses.solve x <: usize) +!
    (f_f #u32 #FStar.Tactics.Typeclasses.solve x <: usize)
    <:
    usize) +!
  (f_f #u32 #FStar.Tactics.Typeclasses.solve x <: usize)
