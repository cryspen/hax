
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

def Tests.Rustc_tests__branch__generics.print_size
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if
  (← Rust_primitives.Hax.Machine_int.gt
      (← Core.Mem.size_of T Rust_primitives.Hax.Tuple0.mk)
      (4 : usize)) then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["size > 4
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["size <= 4
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__generics.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__generics.print_size Rust_primitives.Hax.Tuple0
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__generics.print_size u32
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__generics.print_size u64
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk