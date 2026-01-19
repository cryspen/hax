
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


namespace new_tests.legacy__nested_derefs__lib

def f (x : usize) : RustM usize := do (pure x)

def g (x : usize) : RustM usize := do (f x)

end new_tests.legacy__nested_derefs__lib

