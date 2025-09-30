
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

def Tests.Rustc_tests__try_error_result.call
  (return_error : Bool)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  (← if return_error then do
    (Core.Result.Result.Err Rust_primitives.Hax.Tuple0.mk)
  else do
    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))

def Tests.Rustc_tests__try_error_result.test1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  let countdown : i32 ← (pure (10 : i32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (0 : i32)
        (10 : i32)
        (fun countdown _ => (do true : Result Bool))
        countdown
        (fun countdown _ => (do
            let countdown : i32 ← (pure (← countdown -? (1 : i32)));
            (← if
            (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
              (match (← Tests.Rustc_tests__try_error_result.call true) with
                | (Core.Result.Result.Ok _)
                  => do
                    (match
                      (← Tests.Rustc_tests__try_error_result.call false)
                    with
                      | (Core.Result.Result.Ok _)
                        => do
                          (Core.Ops.Control_flow.ControlFlow.Continue countdown)
                      | (Core.Result.Result.Err err)
                        => do
                          (Core.Ops.Control_flow.ControlFlow.Break
                            (Core.Ops.Control_flow.ControlFlow.Break
                              (Core.Result.Result.Err err))))
                | (Core.Result.Result.Err err)
                  => do
                    (Core.Ops.Control_flow.ControlFlow.Break
                      (Core.Ops.Control_flow.ControlFlow.Break
                        (Core.Result.Result.Err err))))
            else do
              (match (← Tests.Rustc_tests__try_error_result.call false) with
                | (Core.Result.Result.Ok _)
                  => do (Core.Ops.Control_flow.ControlFlow.Continue countdown)
                | (Core.Result.Result.Err err)
                  => do
                    (Core.Ops.Control_flow.ControlFlow.Break
                      (Core.Ops.Control_flow.ControlFlow.Break
                        (Core.Result.Result.Err err))))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  Rust_primitives.Hax.Tuple0
                  Rust_primitives.Hax.Tuple0)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32))
              i32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue countdown)
      => do (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))

structure Tests.Rustc_tests__try_error_result.Thing1 where


structure Tests.Rustc_tests__try_error_result.Thing2 where


def Tests.Rustc_tests__try_error_result.Impl.get_thing_2
  (self : Tests.Rustc_tests__try_error_result.Thing1)
  (return_error : Bool)
  : Result
  (Core.Result.Result
    Tests.Rustc_tests__try_error_result.Thing2
    Rust_primitives.Hax.Tuple0)
  := do
  (← if return_error then do
    (Core.Result.Result.Err Rust_primitives.Hax.Tuple0.mk)
  else do
    (Core.Result.Result.Ok Tests.Rustc_tests__try_error_result.Thing2.mk))

def Tests.Rustc_tests__try_error_result.Impl_1.call
  (self : Tests.Rustc_tests__try_error_result.Thing2)
  (return_error : Bool)
  : Result (Core.Result.Result u32 Rust_primitives.Hax.Tuple0)
  := do
  (← if return_error then do
    (Core.Result.Result.Err Rust_primitives.Hax.Tuple0.mk)
  else do
    (Core.Result.Result.Ok (57 : u32)))

def Tests.Rustc_tests__try_error_result.test2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  let thing1 : Tests.Rustc_tests__try_error_result.Thing1 ← (pure
    Tests.Rustc_tests__try_error_result.Thing1.mk);
  let countdown : i32 ← (pure (10 : i32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (0 : i32)
        (10 : i32)
        (fun countdown _ => (do true : Result Bool))
        countdown
        (fun countdown _ => (do
            let countdown : i32 ← (pure (← countdown -? (1 : i32)));
            (← if
            (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
              (match
                (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                    thing1
                    false)
              with
                | (Core.Result.Result.Ok hoist1)
                  => do
                    let _ ← (pure
                      (← Core.Result.Impl.expect_err
                          u32
                          Rust_primitives.Hax.Tuple0
                          (← Tests.Rustc_tests__try_error_result.Impl_1.call
                              hoist1
                              true)
                          "call should fail"));
                    (match
                      (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                          thing1
                          false)
                    with
                      | (Core.Result.Result.Ok hoist3)
                        => do
                          let _ ← (pure
                            (← Core.Result.Impl.expect_err
                                u32
                                Rust_primitives.Hax.Tuple0
                                (← Tests.Rustc_tests__try_error_result.Impl_1.call
                                    hoist3
                                    true)
                                "call should fail"));
                          (match
                            (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                                thing1
                                true)
                          with
                            | (Core.Result.Result.Ok hoist5)
                              => do
                                (match
                                  (← Tests.Rustc_tests__try_error_result.Impl_1.call
                                      hoist5
                                      true)
                                with
                                  | (Core.Result.Result.Ok val)
                                    => do
                                      let _ ← (pure
                                        (match
                                          (Rust_primitives.Hax.Tuple2.mk
                                            val (57 : u32))
                                        with
                                          | ⟨left_val, right_val⟩
                                            => do
                                              (← Hax_lib.assert
                                                  (← Rust_primitives.Hax.Machine_int.eq
                                                      left_val
                                                      right_val))));
                                      (match
                                        (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                                            thing1
                                            true)
                                      with
                                        | (Core.Result.Result.Ok hoist7)
                                          => do
                                            (match
                                              (← Tests.Rustc_tests__try_error_result.Impl_1.call
                                                  hoist7
                                                  false)
                                            with
                                              | (Core.Result.Result.Ok val)
                                                => do
                                                  let _ ← (pure
                                                    (match
                                                      (Rust_primitives.Hax.Tuple2.mk
                                                        val (57 : u32))
                                                    with
                                                      | ⟨left_val, right_val⟩
                                                        => do
                                                          (← Hax_lib.assert
                                                              (← Rust_primitives.Hax.Machine_int.eq
                                                                  left_val
                                                                  right_val))));
                                                  (Core.Ops.Control_flow.ControlFlow.Continue
                                                    countdown)
                                              | (Core.Result.Result.Err err)
                                                => do
                                                  (Core.Ops.Control_flow.ControlFlow.Break
                                                    (Core.Ops.Control_flow.ControlFlow.Break
                                                      (Core.Result.Result.Err
                                                        err))))
                                        | (Core.Result.Result.Err err)
                                          => do
                                            (Core.Ops.Control_flow.ControlFlow.Break
                                              (Core.Ops.Control_flow.ControlFlow.Break
                                                (Core.Result.Result.Err err))))
                                  | (Core.Result.Result.Err err)
                                    => do
                                      (Core.Ops.Control_flow.ControlFlow.Break
                                        (Core.Ops.Control_flow.ControlFlow.Break
                                          (Core.Result.Result.Err err))))
                            | (Core.Result.Result.Err err)
                              => do
                                (Core.Ops.Control_flow.ControlFlow.Break
                                  (Core.Ops.Control_flow.ControlFlow.Break
                                    (Core.Result.Result.Err err))))
                      | (Core.Result.Result.Err err)
                        => do
                          (Core.Ops.Control_flow.ControlFlow.Break
                            (Core.Ops.Control_flow.ControlFlow.Break
                              (Core.Result.Result.Err err))))
                | (Core.Result.Result.Err err)
                  => do
                    (Core.Ops.Control_flow.ControlFlow.Break
                      (Core.Ops.Control_flow.ControlFlow.Break
                        (Core.Result.Result.Err err))))
            else do
              (match
                (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                    thing1
                    false)
              with
                | (Core.Result.Result.Ok hoist9)
                  => do
                    (match
                      (← Tests.Rustc_tests__try_error_result.Impl_1.call
                          hoist9
                          false)
                    with
                      | (Core.Result.Result.Ok val)
                        => do
                          let _ ← (pure
                            (match
                              (Rust_primitives.Hax.Tuple2.mk val (57 : u32))
                            with
                              | ⟨left_val, right_val⟩
                                => do
                                  (← Hax_lib.assert
                                      (← Rust_primitives.Hax.Machine_int.eq
                                          left_val
                                          right_val))));
                          (match
                            (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                                thing1
                                false)
                          with
                            | (Core.Result.Result.Ok hoist11)
                              => do
                                (match
                                  (← Tests.Rustc_tests__try_error_result.Impl_1.call
                                      hoist11
                                      false)
                                with
                                  | (Core.Result.Result.Ok val)
                                    => do
                                      let _ ← (pure
                                        (match
                                          (Rust_primitives.Hax.Tuple2.mk
                                            val (57 : u32))
                                        with
                                          | ⟨left_val, right_val⟩
                                            => do
                                              (← Hax_lib.assert
                                                  (← Rust_primitives.Hax.Machine_int.eq
                                                      left_val
                                                      right_val))));
                                      (match
                                        (← Tests.Rustc_tests__try_error_result.Impl.get_thing_2
                                            thing1
                                            false)
                                      with
                                        | (Core.Result.Result.Ok hoist13)
                                          => do
                                            (match
                                              (← Tests.Rustc_tests__try_error_result.Impl_1.call
                                                  hoist13
                                                  false)
                                            with
                                              | (Core.Result.Result.Ok val)
                                                => do
                                                  let _ ← (pure
                                                    (match
                                                      (Rust_primitives.Hax.Tuple2.mk
                                                        val (57 : u32))
                                                    with
                                                      | ⟨left_val, right_val⟩
                                                        => do
                                                          (← Hax_lib.assert
                                                              (← Rust_primitives.Hax.Machine_int.eq
                                                                  left_val
                                                                  right_val))));
                                                  (Core.Ops.Control_flow.ControlFlow.Continue
                                                    countdown)
                                              | (Core.Result.Result.Err err)
                                                => do
                                                  (Core.Ops.Control_flow.ControlFlow.Break
                                                    (Core.Ops.Control_flow.ControlFlow.Break
                                                      (Core.Result.Result.Err
                                                        err))))
                                        | (Core.Result.Result.Err err)
                                          => do
                                            (Core.Ops.Control_flow.ControlFlow.Break
                                              (Core.Ops.Control_flow.ControlFlow.Break
                                                (Core.Result.Result.Err err))))
                                  | (Core.Result.Result.Err err)
                                    => do
                                      (Core.Ops.Control_flow.ControlFlow.Break
                                        (Core.Ops.Control_flow.ControlFlow.Break
                                          (Core.Result.Result.Err err))))
                            | (Core.Result.Result.Err err)
                              => do
                                (Core.Ops.Control_flow.ControlFlow.Break
                                  (Core.Ops.Control_flow.ControlFlow.Break
                                    (Core.Result.Result.Err err))))
                      | (Core.Result.Result.Err err)
                        => do
                          (Core.Ops.Control_flow.ControlFlow.Break
                            (Core.Ops.Control_flow.ControlFlow.Break
                              (Core.Result.Result.Err err))))
                | (Core.Result.Result.Err err)
                  => do
                    (Core.Ops.Control_flow.ControlFlow.Break
                      (Core.Ops.Control_flow.ControlFlow.Break
                        (Core.Result.Result.Err err))))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  Rust_primitives.Hax.Tuple0
                  Rust_primitives.Hax.Tuple0)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32))
              i32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue countdown)
      => do (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))

def Tests.Rustc_tests__try_error_result.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0)
  := do
  let _ ← (pure
    (← Core.Result.Impl.expect_err
        Rust_primitives.Hax.Tuple0
        Rust_primitives.Hax.Tuple0
        (← Tests.Rustc_tests__try_error_result.test1
            Rust_primitives.Hax.Tuple0.mk)
        "test1 should fail"));
  (match
    (← Tests.Rustc_tests__try_error_result.test2 Rust_primitives.Hax.Tuple0.mk)
  with
    | (Core.Result.Result.Ok _)
      => do (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))