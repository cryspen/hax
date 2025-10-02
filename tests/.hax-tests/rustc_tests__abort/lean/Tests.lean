
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

def Tests.Rustc_tests__abort.might_abort
  (should_abort : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if should_abort then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["aborting...
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    (← Rust_primitives.Hax.never_to_any
        (← Core.Panicking.panic_fmt
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["panics and aborts"])))
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["Don't Panic
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__abort.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  let countdown : i32 ← (pure (10 : i32));
  let countdown : i32 ← (pure
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
            let _ ← (pure
              (← if
              (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
                let _ ← (pure (← Tests.Rustc_tests__abort.might_abort false));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk));
            let _ ← (pure
              (← if
              (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
                let _ ← (pure (← Tests.Rustc_tests__abort.might_abort false));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk));
            let _ ← (pure
              (← if
              (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
                let _ ← (pure (← Tests.Rustc_tests__abort.might_abort false));
                Rust_primitives.Hax.Tuple0.mk
              else do
                Rust_primitives.Hax.Tuple0.mk));
            let countdown : i32 ← (pure (← countdown -? (1 : i32)));
            countdown : Result i32))));
  (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)