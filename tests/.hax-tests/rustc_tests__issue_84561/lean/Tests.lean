
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

structure Tests.Rustc_tests__issue_84561.Foo where
  _0 : u32

instance Tests.Rustc_tests__issue_84561.Impl_1 :
  Core.Marker.StructuralPartialEq Tests.Rustc_tests__issue_84561.Foo
  where


instance Tests.Rustc_tests__issue_84561.Impl_2 :
  Core.Cmp.PartialEq
  Tests.Rustc_tests__issue_84561.Foo
  Tests.Rustc_tests__issue_84561.Foo
  where


instance Tests.Rustc_tests__issue_84561.Impl_3 :
  Core.Cmp.Eq Tests.Rustc_tests__issue_84561.Foo
  where


instance Tests.Rustc_tests__issue_84561.Impl :
  Core.Fmt.Debug Tests.Rustc_tests__issue_84561.Foo
  where
  fmt (self : Tests.Rustc_tests__issue_84561.Foo) (f : Core.Fmt.Formatter) := do
    let ⟨tmp0, out⟩ ← (pure
      (← Core.Fmt.Impl_11.write_fmt
          f
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["try and succeed"])));
    let f : Core.Fmt.Formatter ← (pure tmp0);
    (match out with
      | (Core.Result.Result.Ok _)
        => do
          let
            hax_temp_output : (Core.Result.Result
              Rust_primitives.Hax.Tuple0
              Core.Fmt.Error) ← (pure
            (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk));
          (Rust_primitives.Hax.Tuple2.mk f hax_temp_output)
      | (Core.Result.Result.Err err)
        => do (Rust_primitives.Hax.Tuple2.mk f (Core.Result.Result.Err err)))

def Tests.Rustc_tests__issue_84561.test3
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let bar : Tests.Rustc_tests__issue_84561.Foo ← (pure
    (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        bar (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let baz : Tests.Rustc_tests__issue_84561.Foo ← (pure
    (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        baz (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_84561.Foo
             (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_84561.Foo bar)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_84561.Foo baz)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (2 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (2 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let bar : Tests.Rustc_tests__issue_84561.Foo ← (pure
    (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        bar (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (4 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_84561.Foo bar)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_84561.Foo
             (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (2 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (2 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let bar : Tests.Rustc_tests__issue_84561.Foo ← (pure
    (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        bar (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (← if is_true then do
      let _ ← (pure
        (match
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
            (Tests.Rustc_tests__issue_84561.Foo.mk (4 : u32)))
        with
          | ⟨left_val, right_val⟩
            => do
              (← Hax_lib.assert
                  (← Core.Ops.Bit.Not.not
                      (← Core.Cmp.PartialEq.eq left_val right_val)))));
      Rust_primitives.Hax.Tuple0.mk
    else do
      let _ ← (pure
        (match
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32))
            (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
        with
          | ⟨left_val, right_val⟩
            => do
              (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if is_true then do
      let _ ← (pure
        (match
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
            (Tests.Rustc_tests__issue_84561.Foo.mk (4 : u32)))
        with
          | ⟨left_val, right_val⟩
            => do
              (← Hax_lib.assert
                  (← Core.Ops.Bit.Not.not
                      (← Core.Cmp.PartialEq.eq left_val right_val)))));
      Rust_primitives.Hax.Tuple0.mk
    else do
      let _ ← (pure
        (match
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32))
            (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
        with
          | ⟨left_val, right_val⟩
            => do
              (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (← if is_true then do
          (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        else do
          (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
        (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32))
        (← if is_true then do
          (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        else do
          (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32))))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (← if is_true then do
          let _ ← (pure
            (match
              (Rust_primitives.Hax.Tuple2.mk
                (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32))
                (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
            with
              | ⟨left_val, right_val⟩
                => do
                  (← Hax_lib.assert
                      (← Core.Cmp.PartialEq.eq left_val right_val))));
          (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
        else do
          let _ ← (pure
            (match
              (Rust_primitives.Hax.Tuple2.mk
                (← if is_true then do
                  (Tests.Rustc_tests__issue_84561.Foo.mk (0 : u32))
                else do
                  (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
                (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32)))
            with
              | ⟨left_val, right_val⟩
                => do
                  (← Hax_lib.assert
                      (← Core.Ops.Bit.Not.not
                          (← Core.Cmp.PartialEq.eq left_val right_val)))));
          (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32)))
        (Tests.Rustc_tests__issue_84561.Foo.mk (5 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (1 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32))
        (Tests.Rustc_tests__issue_84561.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__issue_84561.test1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← if
    (← Rust_primitives.Hax.failure
        "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: expected an arrow type here


Note: the error was labeled with context `DirectAndMut`.
"
        "rust_primitives::hax::failure(
 "ExplicitRejection { reason: \"a node of kind [Raw_pointer] have been found in the AST\" }\n\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n",
 ...")
    then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["debug is enabled
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if
    (← Rust_primitives.Hax.failure
        "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: expected an arrow type here


Note: the error was labeled with context `DirectAndMut`.
"
        "rust_primitives::hax::failure(
 "ExplicitRejection { reason: \"a node of kind [Raw_pointer] have been found in the AST\" }\n\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n",
 ...")
    then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["debug is enabled
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (0 : i32));
  let _ ← (pure
    (← if
    (← Rust_primitives.Hax.failure
        "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: expected an arrow type here


Note: the error was labeled with context `DirectAndMut`.
"
        "rust_primitives::hax::failure(
 "ExplicitRejection { reason: \"a node of kind [Raw_pointer] have been found in the AST\" }\n\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n",
 ...")
    then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["debug is enabled
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Rust_primitives.Hax.failure
        "ExplicitRejection { reason: "a node of kind [Arbitrary_lhs] have been found in the AST" }


Note: the error was labeled with context `reject_ArbitraryLhs`.
"
        "(rust_primitives::hax::failure(
 "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: expected an arrow type here\n\n\nNote: the..."));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (← if
    (← Rust_primitives.Hax.failure
        "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: expected an arrow type here


Note: the error was labeled with context `DirectAndMut`.
"
        "rust_primitives::hax::failure(
 "ExplicitRejection { reason: \"a node of kind [Raw_pointer] have been found in the AST\" }\n\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n",
 ...")
    then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["debug is enabled
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__issue_84561.test2.call_print
  (s : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display String s)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (1 : usize) (1 : usize) #v[""] args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__issue_84561.test2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__issue_84561.test2.call_print
        "called from call_debug: "));
  let _ ← (pure
    (← if
    (← Rust_primitives.Hax.failure
        "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: expected an arrow type here


Note: the error was labeled with context `DirectAndMut`.
"
        "rust_primitives::hax::failure(
 "ExplicitRejection { reason: \"a node of kind [Raw_pointer] have been found in the AST\" }\n\n\nNote: the error was labeled with context `reject_RawOrMutPointer`.\n",
 ...")
    then do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                #v["debug is enabled
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__issue_84561.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__issue_84561.test1 Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__issue_84561.test2 Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__issue_84561.test3 Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk