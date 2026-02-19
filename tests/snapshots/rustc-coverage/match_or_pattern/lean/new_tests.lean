
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


namespace new_tests.rustc_coverage__match_or_pattern

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let a : u8 := (0 : u8);
  let b : u8 := (0 : u8);
  let ⟨a, b⟩ ←
    if is_true then
      let a : u8 := (2 : u8);
      let b : u8 := (0 : u8);
      (pure (rust_primitives.hax.Tuple2.mk a b))
    else
      (pure (rust_primitives.hax.Tuple2.mk a b));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk a b) with
      | ⟨0, 2⟩ | ⟨0, 3⟩ | ⟨1, 2⟩ | ⟨1, 3⟩ =>
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => (pure rust_primitives.hax.Tuple0.mk);
  let ⟨a, b⟩ ←
    if is_true then
      let a : u8 := (0 : u8);
      let b : u8 := (0 : u8);
      (pure (rust_primitives.hax.Tuple2.mk a b))
    else
      (pure (rust_primitives.hax.Tuple2.mk a b));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk a b) with
      | ⟨0, 2⟩ | ⟨0, 3⟩ | ⟨1, 2⟩ | ⟨1, 3⟩ =>
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => (pure rust_primitives.hax.Tuple0.mk);
  let ⟨a, b⟩ ←
    if is_true then
      let a : u8 := (2 : u8);
      let b : u8 := (2 : u8);
      (pure (rust_primitives.hax.Tuple2.mk a b))
    else
      (pure (rust_primitives.hax.Tuple2.mk a b));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk a b) with
      | ⟨0, 2⟩ | ⟨0, 3⟩ | ⟨1, 2⟩ | ⟨1, 3⟩ =>
        (pure rust_primitives.hax.Tuple0.mk)
      | _ => (pure rust_primitives.hax.Tuple0.mk);
  let ⟨a, b⟩ ←
    if is_true then
      let a : u8 := (0 : u8);
      let b : u8 := (2 : u8);
      (pure (rust_primitives.hax.Tuple2.mk a b))
    else
      (pure (rust_primitives.hax.Tuple2.mk a b));
  match (rust_primitives.hax.Tuple2.mk a b) with
    | ⟨0, 2⟩ | ⟨0, 3⟩ | ⟨1, 2⟩ | ⟨1, 3⟩ => (pure rust_primitives.hax.Tuple0.mk)
    | _ => (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__match_or_pattern

