
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

structure Tests.Rustc_tests__partial_eq.Version where
  major : usize
  minor : usize
  patch : usize

instance Tests.Rustc_tests__partial_eq.Impl_1 :
  Core.Clone.Clone Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_2 :
  Core.Fmt.Debug Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_3 :
  Core.Marker.StructuralPartialEq Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_4 :
  Core.Cmp.PartialEq
  Tests.Rustc_tests__partial_eq.Version
  Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_5 :
  Core.Cmp.Eq Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_6 :
  Core.Cmp.PartialOrd
  Tests.Rustc_tests__partial_eq.Version
  Tests.Rustc_tests__partial_eq.Version
  where


instance Tests.Rustc_tests__partial_eq.Impl_7 :
  Core.Cmp.Ord Tests.Rustc_tests__partial_eq.Version
  where


def Tests.Rustc_tests__partial_eq.Impl.new
  (major : usize)
  (minor : usize)
  (patch : usize)
  : Result Tests.Rustc_tests__partial_eq.Version
  := do
  (Tests.Rustc_tests__partial_eq.Version.mk
    (major := major) (minor := minor) (patch := patch))

def Tests.Rustc_tests__partial_eq.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let version_3_2_1 : Tests.Rustc_tests__partial_eq.Version ← (pure
    (← Tests.Rustc_tests__partial_eq.Impl.new
        (3 : usize)
        (2 : usize)
        (1 : usize)));
  let version_3_3_0 : Tests.Rustc_tests__partial_eq.Version ← (pure
    (← Tests.Rustc_tests__partial_eq.Impl.new
        (3 : usize)
        (3 : usize)
        (0 : usize)));
  let
    args : (Rust_primitives.Hax.Tuple3
      Tests.Rustc_tests__partial_eq.Version
      Tests.Rustc_tests__partial_eq.Version
      Bool) ← (pure
    (Rust_primitives.Hax.Tuple3.mk
      version_3_2_1
      version_3_3_0
      (← Core.Cmp.PartialOrd.lt version_3_2_1 version_3_3_0)));
  let args : (RustArray Core.Fmt.Rt.Argument (3 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__partial_eq.Version
             (Rust_primitives.Hax.Tuple0._0 args)),
         (← Core.Fmt.Rt.Impl.new_debug Tests.Rustc_tests__partial_eq.Version
             (Rust_primitives.Hax.Tuple0._1 args)),
         (← Core.Fmt.Rt.Impl.new_display Bool
             (Rust_primitives.Hax.Tuple0._2 args))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (4 : usize) (3 : usize)
            #v["", " < ", " = ", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk