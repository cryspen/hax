module New_tests.Legacy__attributes__lib.Issue_2089_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

class t_Super (v_Self: Type0) = { [@@@ FStar.Tactics.Typeclasses.no_method]f_B:Type0 }

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Super t_S = { f_B = u8 }

class t_T (v_Self: Type0) (v_X: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Super v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_A:Type0;
  f_C:u8;
  f_f_pre:f_A -> prop;
  f_f_post:f_A -> u8 -> prop;
  f_f:x0: f_A -> Prims.Pure u8 (f_f_pre x0) (fun result -> f_f_post x0 result);
  f_g_pre:v_Self -> f_A -> prop;
  f_g_post:v_Self -> f_A -> f_A -> prop;
  f_g:x0: v_Self -> x1: f_A -> Prims.Pure f_A (f_g_pre x0 x1) (fun result -> f_g_post x0 x1 result);
  f_h_pre:
      #v_Y: Type0 ->
      {| i1: Core_models.Convert.t_Into v_Y f_A |} ->
      (_super_i0).f_B ->
      v_Y ->
      v_X
    -> prop;
  f_h_post:
      #v_Y: Type0 ->
      {| i1: Core_models.Convert.t_Into v_Y f_A |} ->
      (_super_i0).f_B ->
      v_Y ->
      v_X ->
      f_A
    -> prop;
  f_h:
      #v_Y: Type0 ->
      {| i1: Core_models.Convert.t_Into v_Y f_A |} ->
      x0: (_super_i0).f_B ->
      x1: v_Y ->
      x2: v_X
    -> Prims.Pure f_A (f_h_pre #v_Y #i1 x0 x1 x2) (fun result -> f_h_post #v_Y #i1 x0 x1 x2 result);
  f_plain_pre:x: u8 -> pred: prop{x >. mk_u8 0 ==> pred};
  f_plain_post:u8 -> u8 -> prop;
  f_plain:x0: u8 -> Prims.Pure u8 (f_plain_pre x0) (fun result -> f_plain_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_X:Type0) {|i: t_T v_Self v_X|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_T t_S u16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_A = u32;
    f_C = mk_u8 1;
    f_f_pre = (fun (x: u32) -> true);
    f_f_post = (fun (x: u32) (out: u8) -> true);
    f_f = (fun (x: u32) -> mk_u8 0);
    f_g_pre = (fun (self: t_S) (x: u32) -> true);
    f_g_post = (fun (self_: t_S) (x: u32) (result: u32) -> true);
    f_g = (fun (self: t_S) (x: u32) -> x);
    f_h_pre
    =
    (fun
        (#v_Y: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_Y u32)
        (x: u8)
        (y: v_Y)
        (z: u16)
        ->
        true);
    f_h_post
    =
    (fun
        (#v_Y: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_Y u32)
        (x: u8)
        (y: v_Y)
        (z: u16)
        (result: u32)
        ->
        true);
    f_h
    =
    (fun
        (#v_Y: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_Y u32)
        (x: u8)
        (y: v_Y)
        (z: u16)
        ->
        Core_models.Convert.f_into #v_Y #u32 #FStar.Tactics.Typeclasses.solve y);
    f_plain_pre = (fun (x: u8) -> x >. mk_u8 0);
    f_plain_post = (fun (x: u8) (out: u8) -> true);
    f_plain = fun (x: u8) -> x
  }
