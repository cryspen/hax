
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


namespace new_tests.rustc_coverage__dead_code

def unused_pub_fn_not_in_library (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (0 : i32);
  if is_true then
    let countdown : i32 := (10 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

def unused_fn (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (0 : i32);
  if is_true then
    let countdown : i32 := (10 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (0 : i32);
  if is_true then
    let countdown : i32 := (10 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__dead_code

