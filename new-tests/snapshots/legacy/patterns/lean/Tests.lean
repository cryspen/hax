
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

structure Tests.Legacy__patterns.Other where
  _0 : i32

inductive Tests.Legacy__patterns.Test : Type
| C1 : Tests.Legacy__patterns.Other -> Tests.Legacy__patterns.Test


def Tests.Legacy__patterns.Impl.test
  (self : Tests.Legacy__patterns.Test)
  : Result i32
  := do
  match self with
    | (Tests.Legacy__patterns.Test.C1 c)
      => (pure (Tests.Legacy__patterns.Other._0 c))