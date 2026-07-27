module New_tests.Legacy__lean_tests__lib.Associated_types.Basic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Iterable (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_first_pre:v_Self -> Type0;
  f_first_post:v_Self -> f_Item -> Type0;
  f_first:x0: v_Self -> Prims.Pure f_Item (f_first_pre x0) (fun result -> f_first_post x0 result)
}

let just_the_first
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterable v_I)
      (iter: v_I)
    : i0.f_Item = f_first #v_I #FStar.Tactics.Typeclasses.solve iter

let first_plus_1_
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterable v_I)
      (#_: unit{i0.f_Item == i32})
      (iter: v_I)
    : i32 = (f_first #v_I #FStar.Tactics.Typeclasses.solve iter <: i32) +! mk_i32 1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Iterable bool =
  {
    f_Item = i32;
    f_first_pre = (fun (self: bool) -> true);
    f_first_post = (fun (self: bool) (out: i32) -> true);
    f_first = fun (self: bool) -> mk_i32 3
  }

let a (_: Prims.unit) : Prims.unit =
  let _:i32 = first_plus_1_ #bool true in
  ()
