
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


namespace new_tests.legacy__if_let__lib

@[spec]
def fun_with_if_let (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let x : (core_models.option.Option u8) :=
    (core_models.option.Option.Some (5 : u8));
  match x with
    | (core_models.option.Option.Some  x) => do (pure x)
    | _ => do (pure (7 : u8))

end new_tests.legacy__if_let__lib

