
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

def Tests.Rustc_tests__sort_groups.generic_fn
  (T : Type) (cond : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if cond then do
    let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
      #v[(← Core.Fmt.Rt.Impl.new_display String
               (← Core.Any.type_name T Rust_primitives.Hax.Tuple0.mk))]);
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
              #v["", "
"]
              args)));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__sort_groups.other_fn
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__sort_groups.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let cond : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.gt
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let _ ← (pure
    (← Tests.Rustc_tests__sort_groups.generic_fn Rust_primitives.Hax.Tuple0
        cond));
  let _ ← (pure
    (← Tests.Rustc_tests__sort_groups.generic_fn String
        (← Core.Ops.Bit.Not.not cond)));
  let _ ← (pure
    (← if (← Core.Hint.black_box Bool false) then do
      let _ ← (pure (← Tests.Rustc_tests__sort_groups.generic_fn Char cond));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (← Tests.Rustc_tests__sort_groups.generic_fn i32 cond));
  let _ ← (pure
    (← Tests.Rustc_tests__sort_groups.other_fn Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk