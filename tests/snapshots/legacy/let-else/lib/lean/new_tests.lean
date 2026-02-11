
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


namespace new_tests.legacy__let_else__lib

def let_else (opt : (core_models.option.Option u32)) : RustM Bool := do
  match opt with
    | (core_models.option.Option.Some  x) => (pure true)
    | _ => (pure false)

def let_else_different_type (opt : (core_models.option.Option u32)) :
    RustM Bool := do
  match opt with
    | (core_models.option.Option.Some  x) =>
      (let_else (core_models.option.Option.Some (← (x +? (1 : u32)))))
    | _ => (pure false)

end new_tests.legacy__let_else__lib

