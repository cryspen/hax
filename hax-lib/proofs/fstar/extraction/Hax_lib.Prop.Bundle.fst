module Hax_lib.Prop.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_lib.Abstraction in
  ()

/// Represent a logical proposition, that may be not computable.
type t_Prop = | Prop : bool -> t_Prop

let impl_7: Core_models.Clone.t_Clone t_Prop =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Marker.t_Copy t_Prop

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Fmt.t_Debug t_Prop

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Hax_lib.Abstraction.t_Abstraction bool =
  {
    f_AbstractType = t_Prop;
    f_lift_pre = (fun (self: bool) -> true);
    f_lift_post = (fun (self: bool) (out: t_Prop) -> true);
    f_lift = fun (self: bool) -> Prop self <: t_Prop
  }

class t_ToProp (v_Self: Type0) = {
  f_to_prop_pre:v_Self -> Type0;
  f_to_prop_post:v_Self -> t_Prop -> Type0;
  f_to_prop:x0: v_Self
    -> Prims.Pure t_Prop (f_to_prop_pre x0) (fun result -> f_to_prop_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_ToProp bool =
  {
    f_to_prop_pre = (fun (self: bool) -> true);
    f_to_prop_post = (fun (self: bool) (out: t_Prop) -> true);
    f_to_prop
    =
    fun (self: bool) -> Hax_lib.Abstraction.f_lift #bool #FStar.Tactics.Typeclasses.solve self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Convert.t_From t_Prop bool =
  {
    f_from_pre = (fun (value: bool) -> true);
    f_from_post = (fun (value: bool) (out: t_Prop) -> true);
    f_from = fun (value: bool) -> Prop value <: t_Prop
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_T t_Prop)
    : Core_models.Ops.Bit.t_BitAnd t_Prop v_T =
  {
    f_Output = t_Prop;
    f_bitand_pre = (fun (self: t_Prop) (rhs: v_T) -> true);
    f_bitand_post = (fun (self: t_Prop) (rhs: v_T) (out: t_Prop) -> true);
    f_bitand
    =
    fun (self: t_Prop) (rhs: v_T) ->
      Prop
      (Core_models.Ops.Bit.f_bitand self._0
          (Core_models.Convert.f_into #v_T #t_Prop #FStar.Tactics.Typeclasses.solve rhs <: t_Prop)
            ._0)
      <:
      t_Prop
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_T t_Prop)
    : Core_models.Ops.Bit.t_BitOr t_Prop v_T =
  {
    f_Output = t_Prop;
    f_bitor_pre = (fun (self: t_Prop) (rhs: v_T) -> true);
    f_bitor_post = (fun (self: t_Prop) (rhs: v_T) (out: t_Prop) -> true);
    f_bitor
    =
    fun (self: t_Prop) (rhs: v_T) ->
      Prop
      (Core_models.Ops.Bit.f_bitor self._0
          (Core_models.Convert.f_into #v_T #t_Prop #FStar.Tactics.Typeclasses.solve rhs <: t_Prop)
            ._0)
      <:
      t_Prop
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core_models.Ops.Bit.t_Not t_Prop =
  {
    f_Output = t_Prop;
    f_not_pre = (fun (self: t_Prop) -> true);
    f_not_post = (fun (self: t_Prop) (out: t_Prop) -> true);
    f_not = fun (self: t_Prop) -> Prop ~.self._0 <: t_Prop
  }

let from_bool (b: bool) : t_Prop = Prop b <: t_Prop

/// Lifts a boolean to a logical proposition.
let impl__from_bool (b: bool) : t_Prop = from_bool b

let v_and (lhs other: t_Prop) : t_Prop = Prop (lhs._0 && other._0) <: t_Prop

/// Conjuction of two propositions.
let impl__and
      (#iimpl_37134320_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_37134320_ t_Prop)
      (self: t_Prop)
      (other: iimpl_37134320_)
    : t_Prop =
  v_and self
    (Core_models.Convert.f_into #iimpl_37134320_ #t_Prop #FStar.Tactics.Typeclasses.solve other
      <:
      t_Prop)

let or (lhs other: t_Prop) : t_Prop = Prop (lhs._0 || other._0) <: t_Prop

/// Disjunction of two propositions.
let impl__or
      (#iimpl_37134320_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_37134320_ t_Prop)
      (self: t_Prop)
      (other: iimpl_37134320_)
    : t_Prop =
  or self
    (Core_models.Convert.f_into #iimpl_37134320_ #t_Prop #FStar.Tactics.Typeclasses.solve other
      <:
      t_Prop)

let not (lhs: t_Prop) : t_Prop = Prop ~.lhs._0 <: t_Prop

/// Negation of a proposition.
let impl__not (self: t_Prop) : t_Prop = not self

/// Logical equality between two value of *any* type
let eq (#v_T: Type0) (e_lhs e_rhs: v_T) : t_Prop = Prop true <: t_Prop

/// Equality between two propositions.
let impl__eq
      (#iimpl_37134320_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_37134320_ t_Prop)
      (self: t_Prop)
      (other: iimpl_37134320_)
    : t_Prop =
  eq #t_Prop
    self
    (Core_models.Convert.f_into #iimpl_37134320_ #t_Prop #FStar.Tactics.Typeclasses.solve other
      <:
      t_Prop)

let ne (#v_T: Type0) (e_lhs e_rhs: v_T) : t_Prop = Prop true <: t_Prop

/// Equality between two propositions.
let impl__ne
      (#iimpl_37134320_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_37134320_ t_Prop)
      (self: t_Prop)
      (other: iimpl_37134320_)
    : t_Prop =
  ne #t_Prop
    self
    (Core_models.Convert.f_into #iimpl_37134320_ #t_Prop #FStar.Tactics.Typeclasses.solve other
      <:
      t_Prop)

let implies__from__constructors (lhs other: t_Prop) : t_Prop = Prop (lhs._0 || ~.other._0) <: t_Prop

/// Logical implication.
let impl__implies
      (#iimpl_37134320_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_37134320_ t_Prop)
      (self: t_Prop)
      (other: iimpl_37134320_)
    : t_Prop =
  implies__from__constructors self
    (Core_models.Convert.f_into #iimpl_37134320_ #t_Prop #FStar.Tactics.Typeclasses.solve other
      <:
      t_Prop)

/// The logical implication `a ==> b`.
let implies
      (#iimpl_979615818_ #iimpl_979615818_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Convert.t_Into iimpl_979615818_ t_Prop)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Convert.t_Into iimpl_648681637_ t_Prop)
      (lhs: iimpl_979615818_)
      (rhs: iimpl_648681637_)
    : t_Prop =
  implies__from__constructors (Core_models.Convert.f_into #iimpl_979615818_
        #t_Prop
        #FStar.Tactics.Typeclasses.solve
        lhs
      <:
      t_Prop)
    (Core_models.Convert.f_into #iimpl_648681637_ #t_Prop #FStar.Tactics.Typeclasses.solve rhs
      <:
      t_Prop)

let v_forall__from__constructors
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_A)
      (e_pred: v_F)
    : t_Prop = Prop true <: t_Prop

/// The universal quantifier. This should be used only for Hax code: in
/// Rust, this is always true.
/// # Example:
/// The Rust expression `forall(|x: T| phi(x))` corresponds to `∀ (x: T), phi(x)`.
let v_forall
      (#v_T #v_U #iimpl_367644862_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_U t_Prop)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn iimpl_367644862_ v_T)
      (f: iimpl_367644862_)
    : t_Prop =
  v_forall__from__constructors #v_T
    (fun x ->
        let x:v_T = x in
        Core_models.Convert.f_into #v_U
          #t_Prop
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Function.f_call #iimpl_367644862_
              #v_T
              #FStar.Tactics.Typeclasses.solve
              f
              (x <: v_T)
            <:
            v_U)
        <:
        t_Prop)

let v_exists__from__constructors
      (#v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_A)
      (e_pred: v_F)
    : t_Prop = Prop true <: t_Prop

/// The existential quantifier. This should be used only for Hax code: in
/// Rust, this is always true.
/// # Example:
/// The Rust expression `exists(|x: T| phi(x))` corresponds to `∃ (x: T), phi(x)`.
let v_exists
      (#v_T #v_U #iimpl_367644862_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_U t_Prop)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn iimpl_367644862_ v_T)
      (f: iimpl_367644862_)
    : t_Prop =
  v_exists__from__constructors #v_T
    (fun x ->
        let x:v_T = x in
        Core_models.Convert.f_into #v_U
          #t_Prop
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Ops.Function.f_call #iimpl_367644862_
              #v_T
              #FStar.Tactics.Typeclasses.solve
              f
              (x <: v_T)
            <:
            v_U)
        <:
        t_Prop)
