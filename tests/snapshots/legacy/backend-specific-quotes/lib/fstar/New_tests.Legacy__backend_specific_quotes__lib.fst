module New_tests.Legacy__backend_specific_quotes__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

let a_verbatim_fstar_definition = 42

let decorated_with_an_fstar_quote (_: Prims.unit) : Prims.unit = ()

let decorated_with_a_coq_quote (_: Prims.unit) : Prims.unit = ()

let decorated_with_a_lean_quote (_: Prims.unit) : Prims.unit = ()

/// Same, but with a `requires` clause: the F* backend looks up the `Requires`
/// role on this item, and used to choke on the unrelated dangling `ItemQuote`
/// marker while doing so.
let quoted_and_decorated (x: u8) : Prims.Pure u8 (requires x <. mk_u8 100) (fun _ -> Prims.l_True) =
  x +! mk_u8 1
