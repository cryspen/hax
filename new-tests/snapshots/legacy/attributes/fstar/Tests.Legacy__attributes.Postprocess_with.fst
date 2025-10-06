module Tests.Legacy__attributes.Postprocess_with
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.trefl ())]

let f (_: Prims.unit) : Prims.unit = ()

[@@FStar.Tactics.postprocess_with ( fun temp_0_ ->
  let ():Prims.unit = temp_0_ in
  Tests.Legacy__attributes.Postprocess_with.Somewhere.some_hypothetical_tactic (mk_u8 12) )]

let g (_: Prims.unit) : Prims.unit = ()
