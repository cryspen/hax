
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


namespace new_tests.rustc_coverage__lazy_boolean

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    ((← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      ==? (1 : usize));
  let ⟨a, b, c⟩ :=
    (rust_primitives.hax.Tuple3.mk (0 : i32) (0 : i32) (0 : i32));
  let ⟨a, b, c⟩ ←
    if is_true then do
      let a : i32 := (1 : i32);
      let b : i32 := (10 : i32);
      let c : i32 := (100 : i32);
      (pure (rust_primitives.hax.Tuple3.mk a b c))
    else do
      (pure (rust_primitives.hax.Tuple3.mk a b c));
  let somebool : Bool ← ((← (a <? b)) ||? (← (b <? c)));
  let somebool : Bool ← ((← (b <? a)) ||? (← (b <? c)));
  let somebool : Bool ← ((← (a <? b)) &&? (← (b <? c)));
  let somebool : Bool ← ((← (b <? a)) &&? (← (b <? c)));
  let a : i32 ←
    if (← (!? is_true)) then do
      let a : i32 := (2 : i32);
      (pure a)
    else do
      (pure a);
  let ⟨b, c⟩ ←
    if is_true then do
      let b : i32 := (30 : i32);
      (pure (rust_primitives.hax.Tuple2.mk b c))
    else do
      let c : i32 := (400 : i32);
      (pure (rust_primitives.hax.Tuple2.mk b c));
  let a : i32 ←
    if (← (!? is_true)) then do
      let a : i32 := (2 : i32);
      (pure a)
    else do
      (pure a);
  if is_true then do
    let b : i32 := (30 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let c : i32 := (400 : i32);
    (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__lazy_boolean
