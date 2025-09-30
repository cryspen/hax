
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

def Tests.Rustc_tests__unreachable.UNREACHABLE_CLOSURE
  : Result Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun _ => (do
      (← Rust_primitives.Hax.never_to_any
          (← Core.Hint.unreachable_unchecked Rust_primitives.Hax.Tuple0.mk)) :
      Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__unreachable.unreachable_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.never_to_any
      (← Core.Hint.unreachable_unchecked Rust_primitives.Hax.Tuple0.mk))

def Tests.Rustc_tests__unreachable.unreachable_intrinsic
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.never_to_any
      (← Core.Intrinsics.unreachable Rust_primitives.Hax.Tuple0.mk))

def Tests.Rustc_tests__unreachable.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← if (← Core.Hint.black_box Bool false) then do
      let _ ← (pure
        (← Tests.Rustc_tests__unreachable.UNREACHABLE_CLOSURE
            Rust_primitives.Hax.Tuple0.mk));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Hint.black_box Bool false) then do
      let _ ← (pure
        (← Tests.Rustc_tests__unreachable.unreachable_function
            Rust_primitives.Hax.Tuple0.mk));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  (← if (← Core.Hint.black_box Bool false) then do
    let _ ← (pure
      (← Tests.Rustc_tests__unreachable.unreachable_intrinsic
          Rust_primitives.Hax.Tuple0.mk));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)