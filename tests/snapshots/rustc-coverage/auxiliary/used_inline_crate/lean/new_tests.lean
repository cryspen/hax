
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


namespace new_tests.rustc_coverage__auxiliary__used_inline_crate

--  @fail(extraction): ssprove(HAX0001)
def used_only_from_bin_crate_generic_function
    (T : Type)
    [trait_constr_used_only_from_bin_crate_generic_function_associated_type_i0 :
      core_models.fmt.Debug.AssociatedTypes
      T]
    [trait_constr_used_only_from_bin_crate_generic_function_i0 :
      core_models.fmt.Debug
      T
      ]
    (arg : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk arg);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug T
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["used_only_from_bin_crate_generic_function with ", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): ssprove(HAX0001)
def used_only_from_this_lib_crate_generic_function
    (T : Type)
    [trait_constr_used_only_from_this_lib_crate_generic_function_associated_type_i0
      : core_models.fmt.Debug.AssociatedTypes
      T]
    [trait_constr_used_only_from_this_lib_crate_generic_function_i0 :
      core_models.fmt.Debug
      T
      ]
    (arg : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk arg);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug T
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["used_only_from_this_lib_crate_generic_function with ", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): ssprove(HAX0001)
def used_from_bin_crate_and_lib_crate_generic_function
    (T : Type)
    [trait_constr_used_from_bin_crate_and_lib_crate_generic_function_associated_type_i0
      : core_models.fmt.Debug.AssociatedTypes
      T]
    [trait_constr_used_from_bin_crate_and_lib_crate_generic_function_i0 :
      core_models.fmt.Debug
      T
      ]
    (arg : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk arg);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug T
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["used_from_bin_crate_and_lib_crate_generic_function with ", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): ssprove(HAX0001)
def used_with_same_type_from_bin_crate_and_lib_crate_generic_function
    (T : Type)
    [trait_constr_used_with_same_type_from_bin_crate_and_lib_crate_generic_function_associated_type_i0
      : core_models.fmt.Debug.AssociatedTypes
      T]
    [trait_constr_used_with_same_type_from_bin_crate_and_lib_crate_generic_function_i0
      : core_models.fmt.Debug
      T
      ]
    (arg : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk arg);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug T
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["used_with_same_type_from_bin_crate_and_lib_crate_generic_function with ",
             "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): ssprove(HAX0001)
def unused_generic_function
    (T : Type)
    [trait_constr_unused_generic_function_associated_type_i0 :
      core_models.fmt.Debug.AssociatedTypes
      T]
    [trait_constr_unused_generic_function_i0 : core_models.fmt.Debug T ]
    (arg : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk arg);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug T
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["unused_generic_function with ", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

def unused_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (2 : i32);
  if (← (core_models.ops.bit.Not.not is_true)) then
    let countdown : i32 := (20 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

def unused_private_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (2 : i32);
  if (← (core_models.ops.bit.Not.not is_true)) then
    let countdown : i32 := (20 : i32);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

def use_this_lib_crate (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (used_from_bin_crate_and_lib_crate_generic_function String
      "used from library used_crate.rs");
  let _ ←
    (used_with_same_type_from_bin_crate_and_lib_crate_generic_function String
      "used from library used_crate.rs");
  let some_vec : (alloc.vec.Vec i32 alloc.alloc.Global) ←
    (alloc.slice.Impl.into_vec i32 alloc.alloc.Global
      (← (rust_primitives.unsize
        #v[(5 : i32), (6 : i32), (7 : i32), (8 : i32)])));
  let _ ←
    (used_only_from_this_lib_crate_generic_function
      (alloc.vec.Vec i32 alloc.alloc.Global) some_vec);
  let _ ←
    (used_only_from_this_lib_crate_generic_function String
      "used ONLY from library used_crate.rs");
  (pure rust_primitives.hax.Tuple0.mk)

def used_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (0 : i32);
  let countdown : i32 ←
    if is_true then
      let countdown : i32 := (10 : i32);
      (pure countdown)
    else
      (pure countdown);
  let _ ← (use_this_lib_crate rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

def used_inline_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let countdown : i32 := (0 : i32);
  let countdown : i32 ←
    if is_true then
      let countdown : i32 := (10 : i32);
      (pure countdown)
    else
      (pure countdown);
  let _ ← (use_this_lib_crate rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__auxiliary__used_inline_crate

