
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


namespace new_tests.rustc_coverage__lazy_boolean

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let ⟨a, b, c⟩ :=
    (rust_primitives.hax.Tuple3.mk (0 : i32) (0 : i32) (0 : i32));
  let ⟨a, b, c⟩ ←
    if is_true then
      let a : i32 := (1 : i32);
      let b : i32 := (10 : i32);
      let c : i32 := (100 : i32);
      (pure (rust_primitives.hax.Tuple3.mk a b c))
    else
      (pure (rust_primitives.hax.Tuple3.mk a b c));
  let somebool : Bool ←
    ((← (rust_primitives.hax.machine_int.lt a b))
      ||? (← (rust_primitives.hax.machine_int.lt b c)));
  let somebool : Bool ←
    ((← (rust_primitives.hax.machine_int.lt b a))
      ||? (← (rust_primitives.hax.machine_int.lt b c)));
  let somebool : Bool ←
    ((← (rust_primitives.hax.machine_int.lt a b))
      &&? (← (rust_primitives.hax.machine_int.lt b c)));
  let somebool : Bool ←
    ((← (rust_primitives.hax.machine_int.lt b a))
      &&? (← (rust_primitives.hax.machine_int.lt b c)));
  let a : i32 ←
    if (← (core_models.ops.bit.Not.not is_true)) then
      let a : i32 := (2 : i32);
      (pure a)
    else
      (pure a);
  let ⟨b, c⟩ ←
    if is_true then
      let b : i32 := (30 : i32);
      (pure (rust_primitives.hax.Tuple2.mk b c))
    else
      let c : i32 := (400 : i32);
      (pure (rust_primitives.hax.Tuple2.mk b c));
  let a : i32 ←
    if (← (core_models.ops.bit.Not.not is_true)) then
      let a : i32 := (2 : i32);
      (pure a)
    else
      (pure a);
  if is_true then
    let b : i32 := (30 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let c : i32 := (400 : i32);
    (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__lazy_boolean

