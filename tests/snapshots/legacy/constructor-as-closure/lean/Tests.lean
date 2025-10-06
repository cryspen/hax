
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

structure Tests.Legacy__constructor_as_closure.Test where
  _0 : i32

def Tests.Legacy__constructor_as_closure.Impl.test
  (x : (Core.Option.Option i32))
  : Result (Core.Option.Option Tests.Legacy__constructor_as_closure.Test)
  := do
  (← Core.Option.Impl.map
      i32
      Tests.Legacy__constructor_as_closure.Test
      i32 -> Result Tests.Legacy__constructor_as_closure.Test
      x
      Tests.Legacy__constructor_as_closure.Test.mk)

inductive Tests.Legacy__constructor_as_closure.Context : Type
| A : i32 -> Tests.Legacy__constructor_as_closure.Context 
| B : i32 -> Tests.Legacy__constructor_as_closure.Context 


def Tests.Legacy__constructor_as_closure.Impl_1.test
  (x : (Core.Option.Option i32))
  : Result (Core.Option.Option Tests.Legacy__constructor_as_closure.Context)
  := do
  (← Core.Option.Impl.map
      i32
      Tests.Legacy__constructor_as_closure.Context
      i32 -> Result Tests.Legacy__constructor_as_closure.Context
      x
      Tests.Legacy__constructor_as_closure.Context.B)