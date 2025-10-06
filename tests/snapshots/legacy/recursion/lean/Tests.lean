
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Tests.Legacy__recursion.f (n : u8) : Result u8 := do
  (← if (← Rust_primitives.Hax.Machine_int.eq n (0 : u8)) then do
    (0 : u8)
  else do
    (← n +? (← Tests.Legacy__recursion.f (← n -? (1 : u8)))))