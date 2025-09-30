
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

def Tests.Rustc_tests__coverage_attr_closure.GLOBAL_CLOSURE_ON
  : Result String -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun input => (do
      let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
        #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                #v["", "
"]
                args)));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__coverage_attr_closure.GLOBAL_CLOSURE_OFF
  : Result String -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun input => (do
      let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
        #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                #v["", "
"]
                args)));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__coverage_attr_closure.contains_closures_on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _local_closure_on : String -> Result Rust_primitives.Hax.Tuple0 ← (pure
    (fun input => (do
        let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
          #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
        let _ ← (pure
          (← Std.Io.Stdio._print
              (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                  #v["", "
"]
                  args)));
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _local_closure_off : String -> Result Rust_primitives.Hax.Tuple0 ← (pure
    (fun input => (do
        let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
          #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
        let _ ← (pure
          (← Std.Io.Stdio._print
              (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                  #v["", "
"]
                  args)));
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__coverage_attr_closure.contains_closures_off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _local_closure_on : String -> Result Rust_primitives.Hax.Tuple0 ← (pure
    (fun input => (do
        let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
          #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
        let _ ← (pure
          (← Std.Io.Stdio._print
              (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                  #v["", "
"]
                  args)));
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _local_closure_off : String -> Result Rust_primitives.Hax.Tuple0 ← (pure
    (fun input => (do
        let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
          #v[(← Core.Fmt.Rt.Impl.new_display String input)]);
        let _ ← (pure
          (← Std.Io.Stdio._print
              (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                  #v["", "
"]
                  args)));
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__coverage_attr_closure.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__coverage_attr_closure.contains_closures_on
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__coverage_attr_closure.contains_closures_off
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk