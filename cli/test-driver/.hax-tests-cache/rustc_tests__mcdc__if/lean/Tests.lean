
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

def Tests.Rustc_tests__mcdc__if.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__if.mcdc_check_neither
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? b) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "a and b"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_check_a
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? b) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "a and b"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_check_b
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? b) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "a and b"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_check_both
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? b) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "a and b"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_check_tree_decision
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? (← b ||? c)) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "pass"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "reject"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_check_not_tree_decision
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← (← a ||? b) &&? c) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "pass"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "reject"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.mcdc_nested_if
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a ||? b) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "a or b"));
    (← if (← b &&? c) then do
      let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "b and c"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk)
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__if.say "neither a nor b"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__if.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_neither false false));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_neither false true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_a true true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_a false true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_b true true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_b true false));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_both false true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_both true true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_check_both true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_tree_decision false true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_tree_decision true true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_tree_decision true false false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_tree_decision true false true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_not_tree_decision
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_not_tree_decision
        true
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_not_tree_decision
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__if.mcdc_check_not_tree_decision
        true
        false
        true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_nested_if true false true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_nested_if true true true));
  let _ ← (pure (← Tests.Rustc_tests__mcdc__if.mcdc_nested_if true true false));
  Rust_primitives.Hax.Tuple0.mk