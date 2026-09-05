module New_tests.Legacy__traits__lib.Implicit_dependencies_issue_667_.Define_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

type t_MyType = | MyType : t_MyType
