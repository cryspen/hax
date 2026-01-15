
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

structure Tests.Legacy__functions.Issue_1048.CallableViaDeref where


instance Tests.Legacy__functions.Issue_1048.Impl :
  Core.Ops.Deref.Deref Tests.Legacy__functions.Issue_1048.CallableViaDeref
  where
  Target := (Rust_primitives.Hax.Tuple0 -> Result Bool)
  deref (self : Tests.Legacy__functions.Issue_1048.CallableViaDeref) := do
    (pure (fun _ => (do (pure true) : Result Bool)))

--  @fail(extraction): coq(HAX0002)
def Tests.Legacy__functions.Issue_1048.call_via_deref
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  ((← (Core.Ops.Deref.Deref.deref
      Tests.Legacy__functions.Issue_1048.CallableViaDeref.mk))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__functions.calling_function_pointer.f
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (pure Rust_primitives.Hax.Tuple0.mk)

--  Issue #757
def Tests.Legacy__functions.calling_function_pointer
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let
    f_ptr : (Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0) :=
    Tests.Legacy__functions.calling_function_pointer.f;
  let _ ←
    (Tests.Legacy__functions.calling_function_pointer.f i32
      Rust_primitives.Hax.Tuple0.mk);
  (pure Rust_primitives.Hax.Tuple0.mk)