
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

class Test_driver.ExtIntoIterator (Self : Type) (T : Type) (U : Type) where
  [_constr_9794153458006678696 : (Core.Iter.Traits.Iterator.Iterator U)]
  unsupported type constraint in trait definition
  expect_le_one :
    Self -> Result (Core.Result.Result (Core.Option.Option T) Anyhow.Error)