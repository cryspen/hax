module Tests.Legacy__constructor_as_closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Test = | Test : i32 -> t_Test

let impl_Test__test (x: Core_models.Option.t_Option i32) : Core_models.Option.t_Option t_Test =
  Core_models.Option.impl__map #i32 #t_Test x Test

type t_Context =
  | Context_A : i32 -> t_Context
  | Context_B : i32 -> t_Context

let impl_Context__test (x: Core_models.Option.t_Option i32) : Core_models.Option.t_Option t_Context =
  Core_models.Option.impl__map #i32 #t_Context x Context_B
