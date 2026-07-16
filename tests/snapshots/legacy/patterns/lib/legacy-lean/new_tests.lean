
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


namespace new_tests.legacy__patterns__lib

structure Other where
  _0 : i32

inductive Test : Type
| C1 : Other -> Test

@[spec]
def Impl.test (self : Test) : RustM i32 := do
  match self with | (Test.C1  c) => do (pure (Other._0 c))

end new_tests.legacy__patterns__lib
