
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

def
  Tests.Rustc_tests__auxiliary__used_crate.used_only_from_bin_crate_generic_function
  (T : Type) [(Core.Fmt.Debug T)] (arg : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug T arg)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["used_only_from_bin_crate_generic_function with ", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__auxiliary__used_crate.used_only_from_this_lib_crate_generic_function
  (T : Type) [(Core.Fmt.Debug T)] (arg : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug T arg)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["used_only_from_this_lib_crate_generic_function with ", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__auxiliary__used_crate.used_from_bin_crate_and_lib_crate_generic_function
  (T : Type) [(Core.Fmt.Debug T)] (arg : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug T arg)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["used_from_bin_crate_and_lib_crate_generic_function with ", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__auxiliary__used_crate.used_with_same_type_from_bin_crate_and_lib_crate_generic_function
  (T : Type) [(Core.Fmt.Debug T)] (arg : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug T arg)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["used_with_same_type_from_bin_crate_and_lib_crate_generic_function with ",
                 "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__used_crate.unused_generic_function
  (T : Type) [(Core.Fmt.Debug T)] (arg : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_debug T arg)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["unused_generic_function with ", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__used_crate.unused_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (2 : i32));
  (← if (← Core.Ops.Bit.Not.not is_true) then do
    let countdown : i32 ← (pure (20 : i32));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__auxiliary__used_crate.unused_private_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (2 : i32));
  (← if (← Core.Ops.Bit.Not.not is_true) then do
    let countdown : i32 ← (pure (20 : i32));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__auxiliary__used_crate.use_this_lib_crate
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__used_crate.used_from_bin_crate_and_lib_crate_generic_function
        String "used from library used_crate.rs"));
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__used_crate.used_with_same_type_from_bin_crate_and_lib_crate_generic_function
        String "used from library used_crate.rs"));
  let some_vec : (Alloc.Vec.Vec i32 Alloc.Alloc.Global) ← (pure
    (← Alloc.Slice.Impl.into_vec i32 Alloc.Alloc.Global
        (← Rust_primitives.unsize
            (← Rust_primitives.Hax.box_new
                #v[(5 : i32), (6 : i32), (7 : i32), (8 : i32)]))));
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__used_crate.used_only_from_this_lib_crate_generic_function
        (Alloc.Vec.Vec i32 Alloc.Alloc.Global) some_vec));
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__used_crate.used_only_from_this_lib_crate_generic_function
        String "used ONLY from library used_crate.rs"));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__used_crate.used_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (0 : i32));
  let countdown : i32 ← (pure
    (← if is_true then do
      let countdown : i32 ← (pure (10 : i32));
      countdown
    else do
      countdown));
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__used_crate.use_this_lib_crate
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk