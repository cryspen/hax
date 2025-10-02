
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

class Test_driver.BackendNameExt (Self : Type) where
  job_kind :
    Self -> Test_driver.Log.BackendJobKind -> Result Test_driver.Log.JobKind