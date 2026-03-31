
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


namespace new_tests.rustc_coverage__macro_in_closure

def NO_BLOCK :
  (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
  :=
  RustM.of_isOk
    (do
    (fun _ =>
      (do
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
            (RustArray.ofVec #v["hello\n"]))));
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0)))
    (by rfl)

def WITH_BLOCK :
  (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
  :=
  RustM.of_isOk
    (do
    (fun _ =>
      (do
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
            (RustArray.ofVec #v["hello\n"]))));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0)))
    (by rfl)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (NO_BLOCK rust_primitives.hax.Tuple0.mk);
  let _ ← (WITH_BLOCK rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__macro_in_closure

