
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

def Tests.Rustc_tests__condition__mod.Conditions.simple_assign
  (a : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure a);
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.assign_and
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a &&? b));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.assign_or
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a ||? b));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.assign_3_or_and
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a ||? (← b &&? c)));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.assign_3_and_or
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← (← a &&? b) ||? c));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.foo
  (a : Bool)
  : Result Bool
  := do
  (← Core.Hint.black_box Bool a)

def Tests.Rustc_tests__condition__mod.Conditions.func_call
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.foo (← a &&? b)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__condition__mod.Conditions.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.simple_assign true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.simple_assign false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_and true false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_and true true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_and false false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_or true false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_or true true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_or false false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_or_and
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_or_and
        true
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_or_and
        false
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_or_and
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_and_or
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_and_or
        true
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_and_or
        false
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.assign_3_and_or
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.func_call true false));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.func_call true true));
  let _ ← (pure
    (← Tests.Rustc_tests__condition__mod.Conditions.func_call false false));
  Rust_primitives.Hax.Tuple0.mk