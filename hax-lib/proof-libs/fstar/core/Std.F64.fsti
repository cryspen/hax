module Std.F64
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

val impl_f64__powf (x y: float) : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)
