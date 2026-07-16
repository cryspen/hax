
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


namespace new_tests.legacy__unsafe__lib

inductive Impossible : Type


@[spec]
def Impossible_cast_to_repr (x : Impossible) :
    RustM rust_primitives.hax.Never := do
  match x with

--  @fail(extraction): coq(HAX0008), ssprove(HAX0008)
def impossible (_ : rust_primitives.hax.Tuple0) : RustM Impossible := do
  (rust_primitives.hax.never_to_any
    (← (core_models.hint.unreachable_unchecked rust_primitives.hax.Tuple0.mk)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def impossible.spec (_ : rust_primitives.hax.Tuple0) :
    Spec
      (requires := do (pure false))
      (ensures := fun _ => pure True)
      (impossible ⟨⟩) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [impossible] <;> bv_decide
}

--  @fail(extraction): coq(HAX0008), ssprove(HAX0008)
def get_unchecked_example (slice : (RustSlice u8)) : RustM u8 := do
  (core_models.slice.Impl.get_unchecked u8 usize slice (6 : usize))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def get_unchecked_example.spec (slice : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (core_models.slice.Impl.len u8 slice)) >? (10 : usize)))
      (ensures := fun _ => pure True)
      (get_unchecked_example (slice : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [get_unchecked_example] <;> bv_decide
}

end new_tests.legacy__unsafe__lib
