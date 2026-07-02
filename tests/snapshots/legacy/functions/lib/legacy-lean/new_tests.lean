
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.legacy__functions__lib

@[spec]
def calling_function_pointer.f (T : Type) (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

--  Issue #757
@[spec]
def calling_function_pointer (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let
    f_ptr : (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0) :=
    calling_function_pointer.f;
  let _ ← (calling_function_pointer.f i32 rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__functions__lib


namespace new_tests.legacy__functions__lib.issue_1048

structure CallableViaDeref where
  -- no fields

@[spec]
def Impl.deref_hoisted (self : CallableViaDeref) :
    RustM (rust_primitives.hax.Tuple0 -> RustM Bool) := do
  (pure (fun _ => (do (pure true) : RustM Bool)))

@[reducible] instance Impl.AssociatedTypes :
  core_models.ops.deref.Deref.AssociatedTypes CallableViaDeref
  where
  Target := (rust_primitives.hax.Tuple0 -> RustM Bool)

instance Impl : core_models.ops.deref.Deref CallableViaDeref where
  deref := (Impl.deref_hoisted)

--  @fail(extraction): coq(HAX0002)
@[spec]
def call_via_deref (_ : rust_primitives.hax.Tuple0) : RustM Bool := do
  ((← (core_models.ops.deref.Deref.deref CallableViaDeref CallableViaDeref.mk))
    rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__functions__lib.issue_1048

