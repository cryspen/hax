
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


namespace new_tests.rustc_coverage__mcdc__nested_if

def say (message : String) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (core_models.hint.black_box String message);
  (pure rust_primitives.hax.Tuple0.mk)

def nested_if_in_condition (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? (← if (← (b ||? c)) then (pure true) else (pure false)))) then
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

def doubly_nested_if_in_condition (a : Bool) (b : Bool) (c : Bool) (d : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (a
    &&? (← if
    (← (b ||? (← if (← (c &&? d)) then (pure true) else (pure false)))) then
      (pure false)
    else
      (pure true)))) then
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

def nested_single_condition_decision (a : Bool) (b : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? (← if b then (pure false) else (pure true)))) then
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

def nested_in_then_block_in_condition
    (a : Bool)
    (b : Bool)
    (c : Bool)
    (d : Bool)
    (e : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if
  (← (a
    &&? (← if (← (b ||? c)) then
      if (← (d &&? e)) then (pure true) else (pure false)
    else
      (pure false)))) then
    let _ ← (say "yes");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "no");
    (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (nested_if_in_condition true false false);
  let _ ← (nested_if_in_condition true true true);
  let _ ← (nested_if_in_condition true false true);
  let _ ← (nested_if_in_condition false true true);
  let _ ← (doubly_nested_if_in_condition true false false true);
  let _ ← (doubly_nested_if_in_condition true true true true);
  let _ ← (doubly_nested_if_in_condition true false true true);
  let _ ← (doubly_nested_if_in_condition false true true true);
  let _ ← (nested_single_condition_decision true true);
  let _ ← (nested_single_condition_decision true false);
  let _ ← (nested_single_condition_decision false false);
  let _ ← (nested_in_then_block_in_condition false false false false false);
  let _ ← (nested_in_then_block_in_condition true false false false false);
  let _ ← (nested_in_then_block_in_condition true true false false false);
  let _ ← (nested_in_then_block_in_condition true false true false false);
  let _ ← (nested_in_then_block_in_condition true false true true false);
  let _ ← (nested_in_then_block_in_condition true false true false true);
  let _ ← (nested_in_then_block_in_condition true false true true true);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__mcdc__nested_if

