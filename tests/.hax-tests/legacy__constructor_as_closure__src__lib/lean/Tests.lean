
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

structure Tests.Legacy__constructor_as_closure__src__lib.Test where
  _0 : i32

def Tests.Legacy__constructor_as_closure__src__lib.Impl.test
  (x : (Core.Option.Option i32))
  : Result
  (Core.Option.Option Tests.Legacy__constructor_as_closure__src__lib.Test)
  := do
  (← Core.Option.Impl.map
      i32
      Tests.Legacy__constructor_as_closure__src__lib.Test
      i32 -> Result Tests.Legacy__constructor_as_closure__src__lib.Test
      x
      Tests.Legacy__constructor_as_closure__src__lib.Test.mk)

inductive Tests.Legacy__constructor_as_closure__src__lib.Context : Type
| A : i32 -> Tests.Legacy__constructor_as_closure__src__lib.Context 
| B : i32 -> Tests.Legacy__constructor_as_closure__src__lib.Context 


def Tests.Legacy__constructor_as_closure__src__lib.Impl_1.test
  (x : (Core.Option.Option i32))
  : Result
  (Core.Option.Option Tests.Legacy__constructor_as_closure__src__lib.Context)
  := do
  (← Core.Option.Impl.map
      i32
      Tests.Legacy__constructor_as_closure__src__lib.Context
      i32 -> Result Tests.Legacy__constructor_as_closure__src__lib.Context
      x
      Tests.Legacy__constructor_as_closure__src__lib.Context.B)