
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


namespace new_tests.rustc_coverage__let_else_loop

--  @fail(extraction): fstar(HAX0001), lean(HAX0001), coq(HAX0001), proverif(HAX0008)
def loopy (cond : Bool) : RustM rust_primitives.hax.Tuple0 := do
  match cond with
    | true => (pure rust_primitives.hax.Tuple0.mk)
    | _ =>
      (pure (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))

--  @fail(extraction): fstar(HAX0001, HAX0001), lean(HAX0001, HAX0001), coq(HAX0001, HAX0001), proverif(HAX0008, HAX0008)
def _loop_either_way (cond : Bool) : RustM rust_primitives.hax.Tuple0 := do
  match cond with
    | true =>
      (rust_primitives.hax.never_to_any
        (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))
    | _ =>
      (pure (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))

--  @fail(extraction): proverif(HAX0008, HAX0008), lean(HAX0001, HAX0001), fstar(HAX0001, HAX0001), coq(HAX0001, HAX0001)
def _if (cond : Bool) : RustM rust_primitives.hax.Tuple0 := do
  if cond then
    (rust_primitives.hax.never_to_any
      (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))
  else
    (rust_primitives.hax.never_to_any
      (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (loopy true);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__let_else_loop

