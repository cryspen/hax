
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

def Tests.Rustc_tests__nested_loops.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (10 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun countdown => (do
            (← Rust_primitives.Hax.Machine_int.gt countdown (0 : i32)) : Result
            Bool))
        (fun countdown => (do true : Result Bool))
        (fun countdown => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        countdown
        (fun countdown => (do
            let a : i32 ← (pure (100 : i32));
            let b : i32 ← (pure (100 : i32));
            let ⟨a, b⟩ ← (pure
              (← Rust_primitives.Hax.Folds.fold_range_cf
                  (0 : i32)
                  (50 : i32)
                  (fun ⟨a, b⟩ _ => (do true : Result Bool))
                  (Rust_primitives.Hax.Tuple2.mk a b)
                  (fun ⟨a, b⟩ _ => (do
                      (← if
                      (← Rust_primitives.Hax.Machine_int.lt a (30 : i32)) then
                      do
                        (Core.Ops.Control_flow.ControlFlow.Break
                          (Rust_primitives.Hax.Tuple2.mk
                            Rust_primitives.Hax.Tuple0.mk
                            (Rust_primitives.Hax.Tuple2.mk a b)))
                      else do
                        let a : i32 ← (pure (← a -? (5 : i32)));
                        let b : i32 ← (pure (← b -? (5 : i32)));
                        (← if
                        (← Rust_primitives.Hax.Machine_int.lt b (90 : i32)) then
                        do
                          let a : i32 ← (pure (← a -? (10 : i32)));
                          (← if is_true then do
                            (Core.Ops.Control_flow.ControlFlow.Break
                              (Rust_primitives.Hax.Tuple2.mk
                                Rust_primitives.Hax.Tuple0.mk
                                (Rust_primitives.Hax.Tuple2.mk a b)))
                          else do
                            let a : i32 ← (pure (← a -? (2 : i32)));
                            (Core.Ops.Control_flow.ControlFlow.Continue
                              (Rust_primitives.Hax.Tuple2.mk a b)))
                        else do
                          (Core.Ops.Control_flow.ControlFlow.Continue
                            (Rust_primitives.Hax.Tuple2.mk a b)))) : Result
                      (Core.Ops.Control_flow.ControlFlow
                        (Rust_primitives.Hax.Tuple2
                          Rust_primitives.Hax.Tuple0
                          (Rust_primitives.Hax.Tuple2 i32 i32))
                        (Rust_primitives.Hax.Tuple2 i32 i32))))));
            (← countdown -? (1 : i32)) : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)