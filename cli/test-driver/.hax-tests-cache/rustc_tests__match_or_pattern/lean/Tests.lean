
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

def Tests.Rustc_tests__match_or_pattern.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let a ← (pure (0 : u8));
  let b ← (pure (0 : u8));
  let ⟨a, b⟩ ← (pure
    (← if is_true then do
      let a : u8 ← (pure (2 : u8));
      let b : u8 ← (pure (0 : u8));
      (Rust_primitives.Hax.Tuple2.mk a b)
    else do
      (Rust_primitives.Hax.Tuple2.mk a b)));
  let _ ← (pure
    (match (Rust_primitives.Hax.Tuple2.mk a b) with
      | ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩ |
        ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩
        => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  let ⟨a, b⟩ ← (pure
    (← if is_true then do
      let a : u8 ← (pure (0 : u8));
      let b : u8 ← (pure (0 : u8));
      (Rust_primitives.Hax.Tuple2.mk a b)
    else do
      (Rust_primitives.Hax.Tuple2.mk a b)));
  let _ ← (pure
    (match (Rust_primitives.Hax.Tuple2.mk a b) with
      | ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩ |
        ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩
        => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  let ⟨a, b⟩ ← (pure
    (← if is_true then do
      let a : u8 ← (pure (2 : u8));
      let b : u8 ← (pure (2 : u8));
      (Rust_primitives.Hax.Tuple2.mk a b)
    else do
      (Rust_primitives.Hax.Tuple2.mk a b)));
  let _ ← (pure
    (match (Rust_primitives.Hax.Tuple2.mk a b) with
      | ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩ |
        ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩
        => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  let ⟨a, b⟩ ← (pure
    (← if is_true then do
      let a : u8 ← (pure (0 : u8));
      let b : u8 ← (pure (2 : u8));
      (Rust_primitives.Hax.Tuple2.mk a b)
    else do
      (Rust_primitives.Hax.Tuple2.mk a b)));
  (match (Rust_primitives.Hax.Tuple2.mk a b) with
    | ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩ |
      ⟨TODO_LINE_622, TODO_LINE_622⟩ | ⟨TODO_LINE_622, TODO_LINE_622⟩
      => do Rust_primitives.Hax.Tuple0.mk
    | _ => do Rust_primitives.Hax.Tuple0.mk)