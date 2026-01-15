
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

def Tests.Legacy__nested_derefs.f (x : usize) : Result usize := do (pure x)

def Tests.Legacy__nested_derefs.g (x : usize) : Result usize := do
  (Tests.Legacy__nested_derefs.f x)