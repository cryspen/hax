
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

structure Test_driver.BackendTestContext where
  test : Test_driver.TestModule
  backend : Hax_types.Cli_options.BackendName
  cache_dir : Std.Path.PathBuf
  haxmeta : Std.Path.PathBuf