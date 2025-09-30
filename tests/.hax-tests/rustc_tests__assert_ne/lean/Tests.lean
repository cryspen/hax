
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

structure Tests.Rustc_tests__assert_ne.Foo where
  _0 : u32

instance Tests.Rustc_tests__assert_ne.Impl :
  Core.Fmt.Debug Tests.Rustc_tests__assert_ne.Foo
  where


instance Tests.Rustc_tests__assert_ne.Impl_1 :
  Core.Marker.StructuralPartialEq Tests.Rustc_tests__assert_ne.Foo
  where


instance Tests.Rustc_tests__assert_ne.Impl_2 :
  Core.Cmp.PartialEq
  Tests.Rustc_tests__assert_ne.Foo
  Tests.Rustc_tests__assert_ne.Foo
  where


def Tests.Rustc_tests__assert_ne.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (← Core.Hint.black_box Tests.Rustc_tests__assert_ne.Foo
            (Tests.Rustc_tests__assert_ne.Foo.mk (5 : u32)))
        (← if (← Core.Hint.black_box Bool false) then do
          (Tests.Rustc_tests__assert_ne.Foo.mk (0 : u32))
        else do
          (Tests.Rustc_tests__assert_ne.Foo.mk (1 : u32))))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk