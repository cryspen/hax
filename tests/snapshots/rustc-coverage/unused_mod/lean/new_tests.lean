
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


namespace new_tests.rustc_coverage__unused_mod.unused_module

def never_called_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        #v["I am never called
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__unused_mod.unused_module


namespace new_tests.rustc_coverage__unused_mod

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        #v["hello world!
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__unused_mod

