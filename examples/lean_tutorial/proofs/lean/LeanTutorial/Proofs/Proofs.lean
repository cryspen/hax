import LeanTutorial.Extraction.Funs
import LeanTutorial.Extraction.Specs
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace lean_tutorial

theorem square.spec.proof (x : Std.U8) : square.spec x := by
  unfold square.spec square
  hax_mvcgen <;> grind [Nat.le_mul_self]

end lean_tutorial
