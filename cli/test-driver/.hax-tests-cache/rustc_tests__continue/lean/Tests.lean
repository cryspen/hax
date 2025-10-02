
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

def Tests.Rustc_tests__continue.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let x : i32 ← (pure (0 : i32));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            (match is_true with
              | TODO_LINE_622 => do x
              | _ => do let x : i32 ← (pure (1 : i32)); (3 : i32)) : Result
            i32))));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            (match is_true with
              | TODO_LINE_622 => do let x : i32 ← (pure (1 : i32)); (3 : i32)
              | _ => do x) : Result i32))));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            (match is_true with
              | TODO_LINE_622 => do let x : i32 ← (pure (1 : i32)); (3 : i32)
              | _ => do x) : Result i32))));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            (← if is_true then do x else do (3 : i32)) : Result i32))));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            let x : i32 ← (pure
              (match is_true with
                | TODO_LINE_622 => do let x : i32 ← (pure (1 : i32)); x
                | _ => do let _ ← (pure x); x));
            let x : i32 ← (pure (3 : i32));
            x : Result i32))));
  let x : i32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range_cf
        (0 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x _ => (do
            (match is_true with
              | TODO_LINE_622
                => do
                  let x : i32 ← (pure (1 : i32));
                  (Core.Ops.Control_flow.ControlFlow.Continue (3 : i32))
              | _
                => do
                  (Core.Ops.Control_flow.ControlFlow.Break
                    (Rust_primitives.Hax.Tuple2.mk
                      Rust_primitives.Hax.Tuple0.mk x))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32)
              i32)))));
  let _ ← (pure x);
  Rust_primitives.Hax.Tuple0.mk