
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


namespace new_tests.legacy__unsafe__lib

inductive Impossible : Type


def Impossible_cast_to_repr (x : Impossible) :
    RustM rust_primitives.hax.Never := do
  match x with 

--  @fail(extraction): coq(HAX0008), ssprove(HAX0008)
def impossible (_ : rust_primitives.hax.Tuple0) : RustM Impossible := do
  (rust_primitives.hax.never_to_any
    (← (core_models.hint.unreachable_unchecked rust_primitives.hax.Tuple0.mk)))

@[spec]
def impossible.spec (_ : rust_primitives.hax.Tuple0) :
    Spec
      (requires := do (pure false))
      (ensures := fun _ => pure True)
      (impossible ⟨⟩) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[impossible] <;> try grind
}

--  @fail(extraction): coq(HAX0008), ssprove(HAX0008)
def get_unchecked_example (slice : (RustSlice u8)) : RustM u8 := do
  (core_models.slice.Impl.get_unchecked u8 usize slice (6 : usize))

@[spec]
def get_unchecked_example.spec (slice : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.machine_int.gt
          (← (core_models.slice.Impl.len u8 slice))
          (10 : usize)))
      (ensures := fun _ => pure True)
      (get_unchecked_example (slice : (RustSlice u8))) := {
  pureRequires := by constructor; mvcgen <;> try grind
  pureEnsures := by constructor; intros; mvcgen <;> try grind
  contract := by mvcgen[get_unchecked_example] <;> try grind
}

end new_tests.legacy__unsafe__lib

