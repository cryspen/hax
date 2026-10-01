
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


namespace new_tests.rustc_coverage__long_and_wide

@[spec]
def wide_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def long_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def far_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (wide_function rust_primitives.hax.Tuple0.mk);
  let _ ← (long_function rust_primitives.hax.Tuple0.mk);
  let _ ← (far_function rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__long_and_wide

