
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


namespace new_tests.legacy__never_type__lib

inductive False : Type


def False_cast_to_repr (x : False) : RustM rust_primitives.hax.Never := do
  match x with 

def never (h : False) : RustM rust_primitives.hax.Never := do match h with 

def test (b : Bool) : RustM u8 := do
  let _ ←
    if b then
      (rust_primitives.hax.never_to_any
        (← (core_models.panicking.panic "explicit panic")))
    else
      (pure rust_primitives.hax.Tuple0.mk);
  (pure (3 : u8))

def any (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T := do
  (rust_primitives.hax.never_to_any
    (← (core_models.panicking.panic "explicit panic")))

end new_tests.legacy__never_type__lib

