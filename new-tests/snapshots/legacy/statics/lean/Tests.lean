
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

def Tests.Legacy__statics.FOO : usize := 0

def Tests.Legacy__statics.get_foo
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  Tests.Legacy__statics.FOO