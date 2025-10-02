
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

def Tests.Rustc_tests__lazy_boolean.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let ⟨a, b, c⟩ ← (pure
    (Rust_primitives.Hax.Tuple3.mk (0 : i32) (0 : i32) (0 : i32)));
  let ⟨a, b, c⟩ ← (pure
    (← if is_true then do
      let a : i32 ← (pure (1 : i32));
      let b : i32 ← (pure (10 : i32));
      let c : i32 ← (pure (100 : i32));
      (Rust_primitives.Hax.Tuple3.mk a b c)
    else do
      (Rust_primitives.Hax.Tuple3.mk a b c)));
  let somebool : Bool ← (pure
    (← (← Rust_primitives.Hax.Machine_int.lt a b)
      ||? (← Rust_primitives.Hax.Machine_int.lt b c)));
  let somebool : Bool ← (pure
    (← (← Rust_primitives.Hax.Machine_int.lt b a)
      ||? (← Rust_primitives.Hax.Machine_int.lt b c)));
  let somebool : Bool ← (pure
    (← (← Rust_primitives.Hax.Machine_int.lt a b)
      &&? (← Rust_primitives.Hax.Machine_int.lt b c)));
  let somebool : Bool ← (pure
    (← (← Rust_primitives.Hax.Machine_int.lt b a)
      &&? (← Rust_primitives.Hax.Machine_int.lt b c)));
  let a : i32 ← (pure
    (← if (← Core.Ops.Bit.Not.not is_true) then do
      let a : i32 ← (pure (2 : i32));
      a
    else do
      a));
  let ⟨b, c⟩ ← (pure
    (← if is_true then do
      let b : i32 ← (pure (30 : i32));
      (Rust_primitives.Hax.Tuple2.mk b c)
    else do
      let c : i32 ← (pure (400 : i32));
      (Rust_primitives.Hax.Tuple2.mk b c)));
  let a : i32 ← (pure
    (← if (← Core.Ops.Bit.Not.not is_true) then do
      let a : i32 ← (pure (2 : i32));
      a
    else do
      a));
  (← if is_true then do
    let b : i32 ← (pure (30 : i32));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let c : i32 ← (pure (400 : i32));
    Rust_primitives.Hax.Tuple0.mk)