
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

def Tests.Rustc_tests__mcdc__nested_if.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__nested_if.nested_if_in_condition
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? (← if (← b ||? c) then do true else do false)) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "yes"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "no"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__nested_if.doubly_nested_if_in_condition
  (a : Bool)
  (b : Bool)
  (c : Bool)
  (d : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if
  (← a
    &&? (← if (← b ||? (← if (← c &&? d) then do true else do false)) then do
      false
    else do
      true)) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "yes"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "no"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__nested_if.nested_single_condition_decision
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if (← a &&? (← if b then do false else do true)) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "yes"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "no"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
  (a : Bool)
  (b : Bool)
  (c : Bool)
  (d : Bool)
  (e : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if
  (← a
    &&? (← if (← b ||? c) then do
      (← if (← d &&? e) then do true else do false)
    else do
      false)) then do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "yes"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__mcdc__nested_if.say "no"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__mcdc__nested_if.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_if_in_condition
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_if_in_condition
        true
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_if_in_condition
        true
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_if_in_condition
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.doubly_nested_if_in_condition
        true
        false
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.doubly_nested_if_in_condition
        true
        true
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.doubly_nested_if_in_condition
        true
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.doubly_nested_if_in_condition
        false
        true
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_single_condition_decision
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_single_condition_decision
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_single_condition_decision
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        false
        false
        false
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        false
        false
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        true
        false
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        false
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        false
        true
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        false
        true
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__nested_if.nested_in_then_block_in_condition
        true
        false
        true
        true
        true));
  Rust_primitives.Hax.Tuple0.mk