
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


namespace new_tests.rustc_coverage__inline_dead

def dead (_ : rust_primitives.hax.Tuple0) : RustM u32 := do (pure (42 : u32))

def live (B : Bool) (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  if B then (dead rust_primitives.hax.Tuple0.mk) else (pure (0 : u32))

--  @fail(extraction): ssprove(HAX0001)
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 u32) :=
    (rust_primitives.hax.Tuple1.mk
      (← (live (false) rust_primitives.hax.Tuple0.mk)));
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_display u32
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  let f : (Bool -> RustM rust_primitives.hax.Tuple0) :=
    (fun x =>
      (do
      let _ ←
        if true then
          let _ ← (hax_lib.assert x);
          (pure rust_primitives.hax.Tuple0.mk)
        else
          (pure rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk) :
      RustM rust_primitives.hax.Tuple0));
  let _ ←
    (core_models.ops.function.Fn.call
      (Bool -> RustM rust_primitives.hax.Tuple0)
      (rust_primitives.hax.Tuple1 Bool)
      f
      (rust_primitives.hax.Tuple1.mk false));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__inline_dead

