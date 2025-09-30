
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

def Tests.Rustc_tests__closure_bug.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let truthy : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let a : Rust_primitives.Hax.Tuple0 -> Result Bool ← (pure
    (fun _ => (do (← if truthy then do true else do false) : Result Bool)));
  let _ ← (pure (← Core.Ops.Function.Fn.call a Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if truthy then do
      let _ ← (pure
        (← Core.Ops.Function.Fn.call a Rust_primitives.Hax.Tuple0.mk));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let b : Rust_primitives.Hax.Tuple0 -> Result Bool ← (pure
    (fun _ => (do (← if truthy then do true else do false) : Result Bool)));
  let _ ← (pure (← Core.Ops.Function.Fn.call b Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if truthy then do
      let _ ← (pure
        (← Core.Ops.Function.Fn.call b Rust_primitives.Hax.Tuple0.mk));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let c : Rust_primitives.Hax.Tuple0 -> Result Bool ← (pure
    (fun _ => (do (← if truthy then do true else do false) : Result Bool)));
  let _ ← (pure (← Core.Ops.Function.Fn.call c Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if truthy then do
      let _ ← (pure
        (← Core.Ops.Function.Fn.call c Rust_primitives.Hax.Tuple0.mk));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let d : Rust_primitives.Hax.Tuple0 -> Result Bool ← (pure
    (fun _ => (do (← if truthy then do true else do false) : Result Bool)));
  let _ ← (pure (← Core.Ops.Function.Fn.call d Rust_primitives.Hax.Tuple0.mk));
  (← if truthy then do
    let _ ← (pure
      (← Core.Ops.Function.Fn.call d Rust_primitives.Hax.Tuple0.mk));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)