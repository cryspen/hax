module Tests.Legacy__cyclic_modules.Bundle_late_skip_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let rec f (_: Prims.unit) : Prims.Pure Prims.unit (requires true) (fun _ -> Prims.l_True) =
  f__from__late_skip_a ()

and f__from__late_skip_a (_: Prims.unit) : Prims.unit = f ()
