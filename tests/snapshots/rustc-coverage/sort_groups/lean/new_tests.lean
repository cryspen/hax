
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


namespace new_tests.rustc_coverage__sort_groups

--  @fail(extraction): ssprove(HAX0001)
def generic_fn (T : Type) (cond : Bool) : RustM rust_primitives.hax.Tuple0 := do
  if cond then
    let args : (rust_primitives.hax.Tuple1 String) :=
      (rust_primitives.hax.Tuple1.mk
        (← (core_models.any.type_name T rust_primitives.hax.Tuple0.mk)));
    let args : (RustArray core_models.fmt.rt.Argument 1) :=
      #v[(← (core_models.fmt.rt.Impl.new_display String
             (rust_primitives.hax.Tuple1._0 args)))];
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
          #v["", "
"]
          args)));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

def other_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let cond : Bool ←
    (rust_primitives.hax.machine_int.gt
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let _ ← (generic_fn rust_primitives.hax.Tuple0 cond);
  let _ ← (generic_fn String (← (core_models.ops.bit.Not.not cond)));
  let _ ←
    if (← (core_models.hint.black_box Bool false)) then
      let _ ← (generic_fn Char cond);
      (pure rust_primitives.hax.Tuple0.mk)
    else
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ← (generic_fn i32 cond);
  let _ ← (other_fn rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__sort_groups

