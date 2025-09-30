
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

def Tests.Rustc_tests__unused.foo
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let i : i32 ← (pure (0 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun i => (do
            (← Rust_primitives.Hax.Machine_int.lt i (10 : i32)) : Result Bool))
        (fun i => (do true : Result Bool))
        (fun i => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        i
        (fun i => (do
            let _ ← (pure
              (← (← Rust_primitives.Hax.Machine_int.ne i (0 : i32))
                ||? (← Rust_primitives.Hax.Machine_int.ne i (0 : i32))));
            let i : i32 ← (pure (← i +? (1 : i32)));
            i : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__unused.unused_template_func
  (T : Type) (x : T)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let i : i32 ← (pure (0 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun i => (do
            (← Rust_primitives.Hax.Machine_int.lt i (10 : i32)) : Result Bool))
        (fun i => (do true : Result Bool))
        (fun i => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        i
        (fun i => (do
            let _ ← (pure
              (← (← Rust_primitives.Hax.Machine_int.ne i (0 : i32))
                ||? (← Rust_primitives.Hax.Machine_int.ne i (0 : i32))));
            let i : i32 ← (pure (← i +? (1 : i32)));
            i : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__unused.unused_func
  (a : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← Rust_primitives.Hax.Machine_int.ne a (0 : u32)) then do
    let a : u32 ← (pure (← a +? (1 : u32)));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__unused.unused_func2
  (a : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← Rust_primitives.Hax.Machine_int.ne a (0 : u32)) then do
    let a : u32 ← (pure (← a +? (1 : u32)));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__unused.unused_func3
  (a : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← Rust_primitives.Hax.Machine_int.ne a (0 : u32)) then do
    let a : u32 ← (pure (← a +? (1 : u32)));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__unused.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  let _ ← (pure (← Tests.Rustc_tests__unused.foo u32 (0 : u32)));
  let _ ← (pure (← Tests.Rustc_tests__unused.foo TODO_LINE_739 TODO_LINE_722));
  (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)