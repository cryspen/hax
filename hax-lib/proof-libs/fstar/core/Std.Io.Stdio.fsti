module Std.Io.Stdio
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

val e_print (args: Core_models.Fmt.t_Arguments)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)
