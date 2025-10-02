
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

def Tests.Rustc_tests__inner_items.main.In_mod.IN_MOD_CONST : u32 := 1000

def Tests.Rustc_tests__inner_items.main.in_func
  (a : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let b : u32 ← (pure (1 : u32));
  let c : u32 ← (pure (← a +? b));
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display u32 c)]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["c = ", "
"]
            args)));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__inner_items.main.InStruct where
  in_struct_field : u32

def Tests.Rustc_tests__inner_items.main.IN_CONST : u32 := 1234

instance Tests.Rustc_tests__inner_items.main.Impl :
  Tests.Rustc_tests__inner_items.main.InTrait
  Tests.Rustc_tests__inner_items.main.InStruct
  where
  trait_func (self : Tests.Rustc_tests__inner_items.main.InStruct)
    (incr : u32)
    := do
    let self : Tests.Rustc_tests__inner_items.main.InStruct ← (pure
      -- Unsupported base expressions for structs.);
    let _ ← (pure
      (← Tests.Rustc_tests__inner_items.main.in_func
          (Tests.Rustc_tests__inner_items.main.InStruct.in_struct_field self)));
    self

def Tests.Rustc_tests__inner_items.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : u32 ← (pure (0 : u32));
  let countdown : u32 ← (pure
    (← if is_true then do
      let countdown : u32 ← (pure (10 : u32));
      countdown
    else do
      countdown));
  let _ ← (pure
    (← if is_true then do
      let _ ← (pure (← Tests.Rustc_tests__inner_items.main.in_func countdown));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let val : Tests.Rustc_tests__inner_items.main.InStruct ← (pure
    (Tests.Rustc_tests__inner_items.main.InStruct.mk
      (in_struct_field := (101 : u32))));
  let val : Tests.Rustc_tests__inner_items.main.InStruct ← (pure
    (← Tests.Rustc_tests__inner_items.main.InTrait.default_trait_func val));
  Rust_primitives.Hax.Tuple0.mk

abbrev Tests.Rustc_tests__inner_items.main.InType := Alloc.String.String