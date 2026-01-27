module Hax_lib.Abstraction
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Marks a type as abstract: its values can be lowered to concrete
/// values. This might panic.
class t_Concretization (v_Self: Type0) (v_T: Type0) = {
  f_concretize_pre:v_Self -> Type0;
  f_concretize_post:v_Self -> v_T -> Type0;
  f_concretize:x0: v_Self
    -> Prims.Pure v_T (f_concretize_pre x0) (fun result -> f_concretize_post x0 result)
}

/// Marks a type as abstractable: its values can be mapped to an
/// idealized version of the type. For instance, machine integers,
/// which have bounds, can be mapped to mathematical integers.
/// Each type can have only one abstraction.
class t_Abstraction (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_AbstractType:Type0;
  f_lift_pre:v_Self -> Type0;
  f_lift_post:v_Self -> f_AbstractType -> Type0;
  f_lift:x0: v_Self
    -> Prims.Pure f_AbstractType (f_lift_pre x0) (fun result -> f_lift_post x0 result)
}
