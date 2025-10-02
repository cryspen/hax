
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

structure Test_driver.TestModule where
  module_name : Alloc.String.String
  def_id : Hax_frontend_exporter.Types.Def_id.DefId
  test_directives : (Alloc.Vec.Vec
      Test_driver.Directives.TestDirective
      Alloc.Alloc.Global)
  items : (Alloc.Vec.Vec
      (Rust_primitives.Hax.Tuple2
        Hax_frontend_exporter.Types.Def_id.DefId
        (Alloc.Vec.Vec Test_driver.Directives.ItemDirective Alloc.Alloc.Global))
      Alloc.Alloc.Global)