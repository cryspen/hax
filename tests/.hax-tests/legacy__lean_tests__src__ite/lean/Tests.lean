
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

def Tests.Legacy__lean_tests__src__ite.test1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result i32
  := do
  let x : i32 ← (pure (← if true then do (0 : i32) else do (1 : i32)));
  (← if false then do (2 : i32) else do (3 : i32))

def Tests.Legacy__lean_tests__src__ite.test2 (b : Bool) : Result i32 := do
  let x : i32 ← (pure
    (← (1 : i32) +? (← if true then do (0 : i32) else do (1 : i32))));
  let y : i32 ← (pure (0 : i32));
  let y : i32 ← (pure
    (← if true then do
      (← (← y +? x) +? (1 : i32))
    else do
      (← (← y -? x) -? (1 : i32))));
  (← if b then do
    let z : i32 ← (pure (← y +? y));
    (← (← z +? y) +? x)
  else do
    let z : i32 ← (pure (← y -? x));
    (← (← z +? y) +? x))