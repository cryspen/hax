module Tests.Legacy__patterns
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Other = | Other : i32 -> t_Other

type t_Test = | Test_C1 : t_Other -> t_Test

let impl__test (self: t_Test) : i32 = match self <: t_Test with | Test_C1 c -> c._0
