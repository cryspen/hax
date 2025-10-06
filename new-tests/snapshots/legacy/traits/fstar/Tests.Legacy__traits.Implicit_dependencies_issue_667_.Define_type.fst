module Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_MyType = | MyType : t_MyType
