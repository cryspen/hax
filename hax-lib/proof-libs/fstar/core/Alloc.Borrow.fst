module Alloc.Borrow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Cow (v_T: Type0) = | Cow : v_T -> t_Cow v_T

class t_ToOwned (v_Self: Type0) = {
  f_to_owned_pre:v_Self -> Type0;
  f_to_owned_post:v_Self -> v_Self -> Type0;
  f_to_owned:x0: v_Self
    -> Prims.Pure v_Self (f_to_owned_pre x0) (fun result -> f_to_owned_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_ToOwned v_T =
  {
    f_to_owned_pre = (fun (self: v_T) -> true);
    f_to_owned_post = (fun (self: v_T) (out: v_T) -> true);
    f_to_owned = fun (self: v_T) -> self
  }
