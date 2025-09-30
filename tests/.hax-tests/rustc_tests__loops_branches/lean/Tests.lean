
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

structure Tests.Rustc_tests__loops_branches.DebugTest where


instance Tests.Rustc_tests__loops_branches.Impl :
  Core.Fmt.Debug Tests.Rustc_tests__loops_branches.DebugTest
  where
  fmt (self : Tests.Rustc_tests__loops_branches.DebugTest)
    (f : Core.Fmt.Formatter)
    := do
    (← if true then do
      let _ ← (pure
        (← if false then do
          (← Rust_primitives.Hax.failure
              "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
              "{
 while true {
 Tuple0
 }
 }")
        else do
          Rust_primitives.Hax.Tuple0.mk));
      let ⟨tmp0, out⟩ ← (pure
        (← Core.Fmt.Impl_11.write_fmt
            f
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["cool"])));
      let f : Core.Fmt.Formatter ← (pure tmp0);
      (match out with
        | (Core.Result.Result.Ok _)
          => do
            (match
              (← Rust_primitives.Hax.Folds.fold_range_return
                  (0 : i32)
                  (10 : i32)
                  (fun f _ => (do true : Result Bool))
                  f
                  (fun f i => (do
                      (← if true then do
                        let _ ← (pure
                          (← if false then do
                            (← Rust_primitives.Hax.failure
                                "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
                                "{
 while true {
 Tuple0
 }
 }")
                          else do
                            Rust_primitives.Hax.Tuple0.mk));
                        let ⟨tmp0, out⟩ ← (pure
                          (← Core.Fmt.Impl_11.write_fmt
                              f
                              (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                                  #v["cool"])));
                        let f : Core.Fmt.Formatter ← (pure tmp0);
                        (match out with
                          | (Core.Result.Result.Ok _)
                            => do (Core.Ops.Control_flow.ControlFlow.Continue f)
                          | (Core.Result.Result.Err err)
                            => do
                              (Core.Ops.Control_flow.ControlFlow.Break
                                (Core.Ops.Control_flow.ControlFlow.Break
                                  (Rust_primitives.Hax.Tuple2.mk
                                    f (Core.Result.Result.Err err)))))
                      else do
                        (Core.Ops.Control_flow.ControlFlow.Continue f)) : Result
                      (Core.Ops.Control_flow.ControlFlow
                        (Core.Ops.Control_flow.ControlFlow
                          (Rust_primitives.Hax.Tuple2
                            Core.Fmt.Formatter
                            (Core.Result.Result
                              Rust_primitives.Hax.Tuple0
                              Core.Fmt.Error))
                          (Rust_primitives.Hax.Tuple2
                            Rust_primitives.Hax.Tuple0
                            Core.Fmt.Formatter))
                        Core.Fmt.Formatter))))
            with
              | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
              | (Core.Ops.Control_flow.ControlFlow.Continue f)
                => do
                  let
                    hax_temp_output : (Core.Result.Result
                      Rust_primitives.Hax.Tuple0
                      Core.Fmt.Error) ← (pure
                    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
                  (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))
        | (Core.Result.Result.Err err)
          => do (Rust_primitives.Hax.Tuple2.mk f (Core.Result.Result.Err err)))
    else do
      (match
        (← Rust_primitives.Hax.Folds.fold_range_return
            (0 : i32)
            (10 : i32)
            (fun f _ => (do true : Result Bool))
            f
            (fun f i => (do
                (← if true then do
                  let _ ← (pure
                    (← if false then do
                      (← Rust_primitives.Hax.failure
                          "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
                          "{
 while true {
 Tuple0
 }
 }")
                    else do
                      Rust_primitives.Hax.Tuple0.mk));
                  let ⟨tmp0, out⟩ ← (pure
                    (← Core.Fmt.Impl_11.write_fmt
                        f
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["cool"])));
                  let f : Core.Fmt.Formatter ← (pure tmp0);
                  (match out with
                    | (Core.Result.Result.Ok _)
                      => do (Core.Ops.Control_flow.ControlFlow.Continue f)
                    | (Core.Result.Result.Err err)
                      => do
                        (Core.Ops.Control_flow.ControlFlow.Break
                          (Core.Ops.Control_flow.ControlFlow.Break
                            (Rust_primitives.Hax.Tuple2.mk
                              f (Core.Result.Result.Err err)))))
                else do
                  (Core.Ops.Control_flow.ControlFlow.Continue f)) : Result
                (Core.Ops.Control_flow.ControlFlow
                  (Core.Ops.Control_flow.ControlFlow
                    (Rust_primitives.Hax.Tuple2
                      Core.Fmt.Formatter
                      (Core.Result.Result
                        Rust_primitives.Hax.Tuple0
                        Core.Fmt.Error))
                    (Rust_primitives.Hax.Tuple2
                      Rust_primitives.Hax.Tuple0
                      Core.Fmt.Formatter))
                  Core.Fmt.Formatter))))
      with
        | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
        | (Core.Ops.Control_flow.ControlFlow.Continue f)
          => do
            let
              hax_temp_output : (Core.Result.Result
                Rust_primitives.Hax.Tuple0
                Core.Fmt.Error) ← (pure
              (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
            (Rust_primitives.Hax.Tuple2.mk f hax_temp_output)))

structure Tests.Rustc_tests__loops_branches.DisplayTest where


instance Tests.Rustc_tests__loops_branches.Impl_1 :
  Core.Fmt.Display Tests.Rustc_tests__loops_branches.DisplayTest
  where
  fmt (self : Tests.Rustc_tests__loops_branches.DisplayTest)
    (f : Core.Fmt.Formatter)
    := do
    (← if false then do
      (match
        (← Rust_primitives.Hax.Folds.fold_range_return
            (0 : i32)
            (10 : i32)
            (fun f _ => (do true : Result Bool))
            f
            (fun f i => (do
                (← if false then do
                  (Core.Ops.Control_flow.ControlFlow.Continue f)
                else do
                  let _ ← (pure
                    (← if false then do
                      (← Rust_primitives.Hax.failure
                          "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
                          "{
 while true {
 Tuple0
 }
 }")
                    else do
                      Rust_primitives.Hax.Tuple0.mk));
                  let ⟨tmp0, out⟩ ← (pure
                    (← Core.Fmt.Impl_11.write_fmt
                        f
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["cool"])));
                  let f : Core.Fmt.Formatter ← (pure tmp0);
                  (match out with
                    | (Core.Result.Result.Ok _)
                      => do (Core.Ops.Control_flow.ControlFlow.Continue f)
                    | (Core.Result.Result.Err err)
                      => do
                        (Core.Ops.Control_flow.ControlFlow.Break
                          (Core.Ops.Control_flow.ControlFlow.Break
                            (Rust_primitives.Hax.Tuple2.mk
                              f (Core.Result.Result.Err err)))))) : Result
                (Core.Ops.Control_flow.ControlFlow
                  (Core.Ops.Control_flow.ControlFlow
                    (Rust_primitives.Hax.Tuple2
                      Core.Fmt.Formatter
                      (Core.Result.Result
                        Rust_primitives.Hax.Tuple0
                        Core.Fmt.Error))
                    (Rust_primitives.Hax.Tuple2
                      Rust_primitives.Hax.Tuple0
                      Core.Fmt.Formatter))
                  Core.Fmt.Formatter))))
      with
        | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
        | (Core.Ops.Control_flow.ControlFlow.Continue f)
          => do
            let
              hax_temp_output : (Core.Result.Result
                Rust_primitives.Hax.Tuple0
                Core.Fmt.Error) ← (pure
              (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
            (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))
    else do
      let _ ← (pure
        (← if false then do
          (← Rust_primitives.Hax.failure
              "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
              "{
 while true {
 Tuple0
 }
 }")
        else do
          Rust_primitives.Hax.Tuple0.mk));
      let ⟨tmp0, out⟩ ← (pure
        (← Core.Fmt.Impl_11.write_fmt
            f
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["cool"])));
      let f : Core.Fmt.Formatter ← (pure tmp0);
      (match out with
        | (Core.Result.Result.Ok _)
          => do
            (match
              (← Rust_primitives.Hax.Folds.fold_range_return
                  (0 : i32)
                  (10 : i32)
                  (fun f _ => (do true : Result Bool))
                  f
                  (fun f i => (do
                      (← if false then do
                        (Core.Ops.Control_flow.ControlFlow.Continue f)
                      else do
                        let _ ← (pure
                          (← if false then do
                            (← Rust_primitives.Hax.failure
                                "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
                                "{
 while true {
 Tuple0
 }
 }")
                          else do
                            Rust_primitives.Hax.Tuple0.mk));
                        let ⟨tmp0, out⟩ ← (pure
                          (← Core.Fmt.Impl_11.write_fmt
                              f
                              (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                                  #v["cool"])));
                        let f : Core.Fmt.Formatter ← (pure tmp0);
                        (match out with
                          | (Core.Result.Result.Ok _)
                            => do (Core.Ops.Control_flow.ControlFlow.Continue f)
                          | (Core.Result.Result.Err err)
                            => do
                              (Core.Ops.Control_flow.ControlFlow.Break
                                (Core.Ops.Control_flow.ControlFlow.Break
                                  (Rust_primitives.Hax.Tuple2.mk
                                    f (Core.Result.Result.Err err)))))) : Result
                      (Core.Ops.Control_flow.ControlFlow
                        (Core.Ops.Control_flow.ControlFlow
                          (Rust_primitives.Hax.Tuple2
                            Core.Fmt.Formatter
                            (Core.Result.Result
                              Rust_primitives.Hax.Tuple0
                              Core.Fmt.Error))
                          (Rust_primitives.Hax.Tuple2
                            Rust_primitives.Hax.Tuple0
                            Core.Fmt.Formatter))
                        Core.Fmt.Formatter))))
            with
              | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
              | (Core.Ops.Control_flow.ControlFlow.Continue f)
                => do
                  let
                    hax_temp_output : (Core.Result.Result
                      Rust_primitives.Hax.Tuple0
                      Core.Fmt.Error) ← (pure
                    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
                  (Rust_primitives.Hax.Tuple2.mk f hax_temp_output))
        | (Core.Result.Result.Err err)
          => do (Rust_primitives.Hax.Tuple2.mk f (Core.Result.Result.Err err))))

def Tests.Rustc_tests__loops_branches.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let debug_test : Tests.Rustc_tests__loops_branches.DebugTest ← (pure
    Tests.Rustc_tests__loops_branches.DebugTest.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__loops_branches.DebugTest
             debug_test)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let display_test : Tests.Rustc_tests__loops_branches.DisplayTest ← (pure
    Tests.Rustc_tests__loops_branches.DisplayTest.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display
             Tests.Rustc_tests__loops_branches.DisplayTest display_test)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk