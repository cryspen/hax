module Tests.Legacy__traits.Type_alias_bounds_issue_707_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_StructWithGenericBounds (v_T: Type0) {| i0: Core_models.Clone.t_Clone v_T |} =
  | StructWithGenericBounds : v_T -> t_StructWithGenericBounds v_T
