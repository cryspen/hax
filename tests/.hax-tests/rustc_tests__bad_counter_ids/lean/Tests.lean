
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

structure Tests.Rustc_tests__bad_counter_ids.Foo where
  _0 : u32

instance Tests.Rustc_tests__bad_counter_ids.Impl :
  Core.Fmt.Debug Tests.Rustc_tests__bad_counter_ids.Foo
  where


instance Tests.Rustc_tests__bad_counter_ids.Impl_1 :
  Core.Marker.StructuralPartialEq Tests.Rustc_tests__bad_counter_ids.Foo
  where


instance Tests.Rustc_tests__bad_counter_ids.Impl_2 :
  Core.Cmp.PartialEq
  Tests.Rustc_tests__bad_counter_ids.Foo
  Tests.Rustc_tests__bad_counter_ids.Foo
  where


instance Tests.Rustc_tests__bad_counter_ids.Impl_3 :
  Core.Cmp.Eq Tests.Rustc_tests__bad_counter_ids.Foo
  where


def Tests.Rustc_tests__bad_counter_ids.eq_good
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["a
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.eq_good_message
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["b
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.ne_good
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["c
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.ne_good_message
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["d
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.eq_bad
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["e
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.eq_bad_message
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["f
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do (← Hax_lib.assert (← Core.Cmp.PartialEq.eq left_val right_val))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.ne_bad
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["g
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.ne_bad_message
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["h
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32))
        (Tests.Rustc_tests__bad_counter_ids.Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩
        => do
          (← Hax_lib.assert
              (← Core.Ops.Bit.Not.not
                  (← Core.Cmp.PartialEq.eq left_val right_val)))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__bad_counter_ids.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__bad_counter_ids.eq_good
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__bad_counter_ids.eq_good_message
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__bad_counter_ids.ne_good
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__bad_counter_ids.ne_good_message
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Hax_lib.assert
        (← Core.Result.Impl.is_err
            Rust_primitives.Hax.Tuple0
            (Alloc.Boxed.Box sorry 
-- unsupported type
 Alloc.Alloc.Global)
            (← Std.Panic.catch_unwind
                Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0
                Tests.Rustc_tests__bad_counter_ids.eq_bad))));
  let _ ← (pure
    (← Hax_lib.assert
        (← Core.Result.Impl.is_err
            Rust_primitives.Hax.Tuple0
            (Alloc.Boxed.Box sorry 
-- unsupported type
 Alloc.Alloc.Global)
            (← Std.Panic.catch_unwind
                Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0
                Tests.Rustc_tests__bad_counter_ids.eq_bad_message))));
  let _ ← (pure
    (← Hax_lib.assert
        (← Core.Result.Impl.is_err
            Rust_primitives.Hax.Tuple0
            (Alloc.Boxed.Box sorry 
-- unsupported type
 Alloc.Alloc.Global)
            (← Std.Panic.catch_unwind
                Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0
                Tests.Rustc_tests__bad_counter_ids.ne_bad))));
  let _ ← (pure
    (← Hax_lib.assert
        (← Core.Result.Impl.is_err
            Rust_primitives.Hax.Tuple0
            (Alloc.Boxed.Box sorry 
-- unsupported type
 Alloc.Alloc.Global)
            (← Std.Panic.catch_unwind
                Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0
                Tests.Rustc_tests__bad_counter_ids.ne_bad_message))));
  Rust_primitives.Hax.Tuple0.mk