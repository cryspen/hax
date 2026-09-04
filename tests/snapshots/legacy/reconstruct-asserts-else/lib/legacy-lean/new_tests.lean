
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.legacy__reconstruct_asserts_else__lib

--  Value in the else branch.
@[spec]
def checked_incr (c : Bool) (x : u32) : RustM u32 := do
  let _ ← (hax_lib.assert (← (!? c)));
  (x +? (1 : u32))

--  Nested panic-elses.
@[spec]
def nested (c : Bool) (d : Bool) (x : u32) : RustM u32 := do
  let _ ← (hax_lib.assert (← (!? c)));
  let _ ← (hax_lib.assert (← (!? d)));
  (pure x)

--  No else.
@[spec]
def bare (c : Bool) : RustM rust_primitives.hax.Tuple0 := do
  (hax_lib.assert (← (!? c)))

end new_tests.legacy__reconstruct_asserts_else__lib

