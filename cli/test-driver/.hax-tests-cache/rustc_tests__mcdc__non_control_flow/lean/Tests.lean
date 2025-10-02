
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

def Tests.Rustc_tests__mcdc__non_control_flow.assign_and
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a &&? b));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.assign_or
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a ||? b));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.assign_3
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a ||? (← b &&? c)));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.assign_3_bis
  (a : Bool)
  (b : Bool)
  (c : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← (← a &&? b) ||? c));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.right_comb_tree
  (a : Bool)
  (b : Bool)
  (c : Bool)
  (d : Bool)
  (e : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let x : Bool ← (pure (← a &&? (← b &&? (← c &&? (← d &&? e)))));
  let _ ← (pure (← Core.Hint.black_box Bool x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.foo (a : Bool) : Result Bool := do
  (← Core.Hint.black_box Bool a)

def Tests.Rustc_tests__mcdc__non_control_flow.func_call
  (a : Bool)
  (b : Bool)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Tests.Rustc_tests__mcdc__non_control_flow.foo (← a &&? b)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__mcdc__non_control_flow.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_and true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_and true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_and false false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_or true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_or true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_or false false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3 true false false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3 true true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3 false false true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3 false true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3_bis
        true
        false
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3_bis true true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3_bis
        false
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.assign_3_bis false true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.right_comb_tree
        false
        false
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.right_comb_tree
        true
        false
        false
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.right_comb_tree
        true
        true
        true
        true
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.func_call true false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.func_call true true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__non_control_flow.func_call false false));
  Rust_primitives.Hax.Tuple0.mk