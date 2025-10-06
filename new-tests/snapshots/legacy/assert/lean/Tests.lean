
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

def Tests.Legacy__assert.asserts
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Hax_lib.assert true));
  let _ ← (pure
    (← Hax_lib.assert
        (← Rust_primitives.Hax.Machine_int.eq (1 : i32) (1 : i32))));
  let _ ← (pure
    (match (Rust_primitives.Hax.Tuple2.mk (2 : i32) (2 : i32)) with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Rust_primitives.Hax.Machine_int.eq left_val right_val))));
  let _ ← (pure
    (match (Rust_primitives.Hax.Tuple2.mk (1 : i32) (2 : i32)) with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Rust_primitives.Hax.Machine_int.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk