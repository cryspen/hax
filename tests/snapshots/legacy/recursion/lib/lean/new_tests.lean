
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


namespace new_tests.legacy__recursion__lib

def f (n : u8) : RustM u8 := do
  if (← (rust_primitives.hax.machine_int.eq n (0 : u8))) then
    (pure (0 : u8))
  else
    (n +? (← (f (← (n -? (1 : u8))))))

end new_tests.legacy__recursion__lib

