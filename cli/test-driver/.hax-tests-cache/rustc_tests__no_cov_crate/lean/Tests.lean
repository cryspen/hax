
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

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_not_covered.inner
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if is_true then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["called and covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["absolutely not covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_not_covered
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called but not covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_not_covered.inner
        is_true));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer.inner_not_covered
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if is_true then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["called but not covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["absolutely not covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called and covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer.inner_not_covered
        is_true));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_both_covered.inner
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if is_true then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["called and covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["absolutely not covered
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_both_covered
  (is_true : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called and covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_both_covered.inner
        is_true));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.do_not_add_coverage_1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called but not covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.do_not_add_coverage_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called but not covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.do_not_add_coverage_not_called
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["not called and not covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.add_coverage_1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called and covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.add_coverage_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["called and covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.add_coverage_not_called
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
            #v["not called but covered
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__no_cov_crate.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.do_not_add_coverage_1
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.do_not_add_coverage_2
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.add_coverage_1
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.add_coverage_2
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_not_covered is_true));
  let _ ← (pure (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer is_true));
  let _ ← (pure
    (← Tests.Rustc_tests__no_cov_crate.Nested_fns.outer_both_covered is_true));
  Rust_primitives.Hax.Tuple0.mk