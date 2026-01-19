
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


namespace new_tests.legacy__assert__lib

def asserts (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (hax_lib.assert true);
  let _ ←
    (hax_lib.assert
      (← (rust_primitives.hax.machine_int.eq (1 : i32) (1 : i32))));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk (2 : i32) (2 : i32)) with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (rust_primitives.hax.machine_int.eq left_val right_val)));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk (1 : i32) (2 : i32)) with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (rust_primitives.hax.machine_int.eq left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__assert__lib

