module Tests.Legacy__cyclic_modules.Bundle_variant_constructor_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Context =
  | Context_A : i32 -> t_Context
  | Context_B : i32 -> t_Context

let impl__test (x: Core_models.Option.t_Option i32) : Core_models.Option.t_Option t_Context =
  Core_models.Option.impl__map #i32 #t_Context x Context_A

let h (_: Prims.unit) : t_Context = Context_A (mk_i32 1) <: t_Context

let f (_: Prims.unit) : t_Context = h ()
