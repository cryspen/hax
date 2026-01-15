module Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_MyType = | MyType : t_MyType
