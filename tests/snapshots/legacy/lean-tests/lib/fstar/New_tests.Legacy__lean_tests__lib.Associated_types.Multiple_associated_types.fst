module New_tests.Legacy__lean_tests__lib.Associated_types.Multiple_associated_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Pair (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_First:Type0;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Second:Type0;
  f_first_pre:v_Self -> Type0;
  f_first_post:v_Self -> f_First -> Type0;
  f_first:x0: v_Self -> Prims.Pure f_First (f_first_pre x0) (fun result -> f_first_post x0 result);
  f_second_pre:v_Self -> Type0;
  f_second_post:v_Self -> f_Second -> Type0;
  f_second:x0: v_Self
    -> Prims.Pure f_Second (f_second_pre x0) (fun result -> f_second_post x0 result)
}

let get_both (#v_P: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Pair v_P) (pair: v_P)
    : (i0.f_First & i0.f_Second) =
  f_first #v_P #FStar.Tactics.Typeclasses.solve pair,
  f_second #v_P #FStar.Tactics.Typeclasses.solve pair
  <:
  (i0.f_First & i0.f_Second)

/// @fail(extraction): ssprove(HAX0001)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Pair (i32 & bool) =
  {
    f_First = i32;
    f_Second = bool;
    f_first_pre = (fun (self: (i32 & bool)) -> true);
    f_first_post = (fun (self: (i32 & bool)) (out: i32) -> true);
    f_first = (fun (self: (i32 & bool)) -> self._1);
    f_second_pre = (fun (self: (i32 & bool)) -> true);
    f_second_post = (fun (self: (i32 & bool)) (out: bool) -> true);
    f_second = fun (self: (i32 & bool)) -> self._2
  }

let b (_: Prims.unit) : Prims.unit =
  let pair:(i32 & bool) = mk_i32 42, true <: (i32 & bool) in
  let both:(i32 & bool) = get_both #(i32 & bool) pair in
  ()

let get_first_as_i32
      (#v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Pair v_P)
      (#_: unit{i0.f_First == i32})
      (pair: v_P)
    : i32 = f_first #v_P #FStar.Tactics.Typeclasses.solve pair
