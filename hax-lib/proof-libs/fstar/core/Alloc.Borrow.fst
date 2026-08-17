module Alloc.Borrow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::borrow::ToOwned`]
class t_ToOwned (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Owned:Type0;
  f_to_owned_pre:v_Self -> Type0;
  f_to_owned_post:v_Self -> f_Owned -> Type0;
  f_to_owned:x0: v_Self
    -> Prims.Pure f_Owned (f_to_owned_pre x0) (fun result -> f_to_owned_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
    : t_ToOwned v_T =
  {
    f_Owned = v_T;
    f_to_owned_pre = (fun (self: v_T) -> true);
    f_to_owned_post = (fun (self: v_T) (out: v_T) -> true);
    f_to_owned
    =
    fun (self: v_T) -> Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve self
  }

/// See [`std::borrow::Cow`]: std's two variants, with the `&'a B` of
/// `Borrowed` erased to a plain `B` as hax erases shared borrows.
type t_Cow (v_B: Type0) {| i0: t_ToOwned v_B |} =
  | Cow_Borrowed : v_B -> t_Cow v_B
  | Cow_Owned : i0.f_Owned -> t_Cow v_B

/// See [`std::borrow::Cow::is_borrowed`]. Like std's, an associated
/// function rather than a method, so it cannot clash with a method of
/// the inner type.
let impl_1__is_borrowed
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_ToOwned v_B)
      (c: t_Cow v_B)
    : bool =
  match c <: t_Cow v_B with
  | Cow_Borrowed _ -> true
  | Cow_Owned _ -> false

/// See [`std::borrow::Cow::is_owned`]
let impl_1__is_owned
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_ToOwned v_B)
      (c: t_Cow v_B)
    : bool =
  match c <: t_Cow v_B with
  | Cow_Borrowed _ -> false
  | Cow_Owned _ -> true

/// See [`std::borrow::Cow::into_owned`]
let impl_1__into_owned
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_ToOwned v_B)
      (self: t_Cow v_B)
    : i0.f_Owned =
  match self <: t_Cow v_B with
  | Cow_Borrowed b -> f_to_owned #v_B #FStar.Tactics.Typeclasses.solve b
  | Cow_Owned o -> o

/// See [`std::borrow::Cow::to_mut`].
let impl_1__to_mut
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_ToOwned v_B)
      (self: t_Cow v_B)
    : i0.f_Owned = impl_1__into_owned #v_B self

/// `clone_into` is a trait *default* method in real `alloc`, which hax does
/// not support. Like `core::cmp`'s `Neq` / `PartialOrdDefaults`, the model
/// provides it through a blanket-implemented companion trait.
class t_ToOwnedDefaults (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_ToOwned v_Self;
  f_clone_into_pre:v_Self -> (_super_i0).f_Owned -> Type0;
  f_clone_into_post:v_Self -> (_super_i0).f_Owned -> (_super_i0).f_Owned -> Type0;
  f_clone_into:x0: v_Self -> x1: (_super_i0).f_Owned
    -> Prims.Pure (_super_i0).f_Owned
        (f_clone_into_pre x0 x1)
        (fun result -> f_clone_into_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_ToOwnedDefaults v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_ToOwned v_T)
    : t_ToOwnedDefaults v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_clone_into_pre = (fun (self: v_T) (target: i0.f_Owned) -> true);
    f_clone_into_post = (fun (self: v_T) (target: i0.f_Owned) (out: i0.f_Owned) -> true);
    f_clone_into
    =
    fun (self: v_T) (target: i0.f_Owned) ->
      let target = f_to_owned #v_T #FStar.Tactics.Typeclasses.solve self in
      target
  }
