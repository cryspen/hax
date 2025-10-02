
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

def Tests.Rustc_tests__overflow.might_overflow (to_add : u32) : Result u32 := do
  let _ ← (pure
    (← if (← Rust_primitives.Hax.Machine_int.gt to_add (5 : u32)) then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["this will probably overflow
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let add_to : u32 ← (pure (← Core.Num.Impl_8.MAX -? (5 : u32)));
  let args : (Rust_primitives.Hax.Tuple2 u32 u32) ← (pure
    (Rust_primitives.Hax.Tuple2.mk add_to to_add));
  let args : (RustArray Core.Fmt.Rt.Argument (2 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display u32
             (Rust_primitives.Hax.Tuple0._0 args)),
         (← Core.Fmt.Rt.Impl.new_display u32
             (Rust_primitives.Hax.Tuple0._1 args))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (3 : usize) (2 : usize)
            #v["does ", " + ", " overflow?
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let result : u32 ← (pure (← to_add +? add_to));
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["continuing after overflow check
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  result

def Tests.Rustc_tests__overflow.main
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
              (← Rust_primitives.Hax.Machine_int.eq countdown (1 : i32)) then do
                let result : u32 ← (pure
                  (← Tests.Rustc_tests__overflow.might_overflow (10 : u32)));
                let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
                  #v[(← Core.Fmt.Rt.Impl.new_display u32 result)]);
                let _ ← (pure
                  (← Std.Io.Stdio._print
                      (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                          #v["Result: ", "
"]
                          args)));
                let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                Rust_primitives.Hax.Tuple0.mk
              else do
                (← if
                (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then
                do
                  let result : u32 ← (pure
                    (← Tests.Rustc_tests__overflow.might_overflow (1 : u32)));
                  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ←
                    (pure #v[(← Core.Fmt.Rt.Impl.new_display u32 result)]);
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                            #v["Result: ", "
"]
                            args)));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  Rust_primitives.Hax.Tuple0.mk)));
            let countdown : i32 ← (pure (← countdown -? (1 : i32)));
            countdown : Result i32))));
  (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)