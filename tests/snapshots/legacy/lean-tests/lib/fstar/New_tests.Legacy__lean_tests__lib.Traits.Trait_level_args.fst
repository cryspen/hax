module New_tests.Legacy__lean_tests__lib.Traits.Trait_level_args
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_T1 (v_Self: Type0) (v_A: Type0) (v_B: Type0) = {
  f_f1_pre:#v_C: Type0 -> #v_D: Type0 -> v_Self -> Type0;
  f_f1_post:#v_C: Type0 -> #v_D: Type0 -> v_Self -> Prims.unit -> Type0;
  f_f1:#v_C: Type0 -> #v_D: Type0 -> x0: v_Self
    -> Prims.Pure Prims.unit (f_f1_pre #v_C #v_D x0) (fun result -> f_f1_post #v_C #v_D x0 result);
  f_f2_pre:#v_C: Type0 -> #v_D: Type0 -> v_Self -> v_A -> Type0;
  f_f2_post:#v_C: Type0 -> #v_D: Type0 -> v_Self -> v_A -> Prims.unit -> Type0;
  f_f2:#v_C: Type0 -> #v_D: Type0 -> x0: v_Self -> x1: v_A
    -> Prims.Pure Prims.unit
        (f_f2_pre #v_C #v_D x0 x1)
        (fun result -> f_f2_post #v_C #v_D x0 x1 result);
  f_f3_pre:#v_C: Type0 -> #v_D: Type0 -> v_Self -> v_A -> v_B -> Type0;
  f_f3_post:#v_C: Type0 -> #v_D: Type0 -> v_Self -> v_A -> v_B -> Prims.unit -> Type0;
  f_f3:#v_C: Type0 -> #v_D: Type0 -> x0: v_Self -> x1: v_A -> x2: v_B
    -> Prims.Pure Prims.unit
        (f_f3_pre #v_C #v_D x0 x1 x2)
        (fun result -> f_f3_post #v_C #v_D x0 x1 x2 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T1 usize u32 u64 =
  {
    f_f1_pre = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) -> true);
    f_f1_post = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (out: Prims.unit) -> true);
    f_f1 = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) -> ());
    f_f2_pre = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) -> true);
    f_f2_post = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) (out: Prims.unit) -> true);
    f_f2 = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) -> ());
    f_f3_pre = (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) (y: u64) -> true);
    f_f3_post
    =
    (fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) (y: u64) (out: Prims.unit) -> true);
    f_f3 = fun (#v_C: Type0) (#v_D: Type0) (self: usize) (x: u32) (y: u64) -> ()
  }

let test
      (#v_A #v_B #v_C #v_D #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_T1 v_U v_A v_B)
      (x: v_U)
      (a: v_A)
      (b: v_B)
    : Prims.unit =
  let _:Prims.unit = f_f1 #v_U #v_A #v_B #FStar.Tactics.Typeclasses.solve #v_C #v_D x in
  let _:Prims.unit = f_f2 #v_U #v_A #v_B #FStar.Tactics.Typeclasses.solve #v_C #v_D x a in
  let _:Prims.unit = f_f3 #v_U #v_A #v_B #FStar.Tactics.Typeclasses.solve #v_C #v_D x a b in
  ()
