module Tests.Legacy__constructor_as_closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Test = | Test : i32 -> t_Test

let impl_Test__test (x: Core.Option.t_Option i32) : Core.Option.t_Option t_Test =
  Core.Option.impl__map #i32 #t_Test x Test

type t_Context =
  | Context_A : i32 -> t_Context
  | Context_B : i32 -> t_Context

let impl_Context__test (x: Core.Option.t_Option i32) : Core.Option.t_Option t_Context =
  Core.Option.impl__map #i32 #t_Context x Context_B
