module Tests.Legacy__traits.Type_alias_bounds_issue_707_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_StructWithGenericBounds (v_T: Type0) {| i0: Core.Clone.t_Clone v_T |} =
  | StructWithGenericBounds : v_T -> t_StructWithGenericBounds v_T
