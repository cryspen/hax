
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

structure Tests.Rustc_tests__issue_83601.Foo where
  _0 : u32

instance Tests.Rustc_tests__issue_83601.Impl :
  Core.Fmt.Debug Tests.Rustc_tests__issue_83601.Foo
  where


instance Tests.Rustc_tests__issue_83601.Impl_1 :
  Core.Marker.StructuralPartialEq Tests.Rustc_tests__issue_83601.Foo
  where


instance Tests.Rustc_tests__issue_83601.Impl_2 :
  Core.Cmp.PartialEq
  Tests.Rustc_tests__issue_83601.Foo
  Tests.Rustc_tests__issue_83601.Foo
  where


instance Tests.Rustc_tests__issue_83601.Impl_3 :
  Core.Cmp.Eq Tests.Rustc_tests__issue_83601.Foo
  where


def Tests.Rustc_tests__issue_83601.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let bar : Tests.Rustc_tests__issue_83601.Foo ← (pure
    (Tests.Rustc_tests__issue_83601.Foo.mk (1 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        bar (Tests.Rustc_tests__issue_83601.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  let baz : Tests.Rustc_tests__issue_83601.Foo ← (pure
    (Tests.Rustc_tests__issue_83601.Foo.mk (0 : u32)));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        baz (Tests.Rustc_tests__issue_83601.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_83601.Foo
             (Tests.Rustc_tests__issue_83601.Foo.mk (1 : u32)))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_83601.Foo bar)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__issue_83601.Foo baz)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk