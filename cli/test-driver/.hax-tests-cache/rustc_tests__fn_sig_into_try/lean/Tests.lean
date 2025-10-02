
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

def Tests.Rustc_tests__fn_sig_into_try.a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Option.Option i32)
  := do
  let _ ← (pure (Core.Option.Option.Some (7 : i32)));
  (Core.Option.Option.Some (0 : i32))

def Tests.Rustc_tests__fn_sig_into_try.b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Option.Option i32)
  := do
  (match (Core.Option.Option.Some (7 : i32)) with
    | (Core.Option.Option.Some _) => do (Core.Option.Option.Some (0 : i32))
    | (Core.Option.Option.None ) => do Core.Option.Option.None)

def Tests.Rustc_tests__fn_sig_into_try.c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Option.Option i32)
  := do
  (match (Core.Option.Option.Some (7 : i32)) with
    | (Core.Option.Option.Some _) => do (Core.Option.Option.Some (0 : i32))
    | (Core.Option.Option.None ) => do Core.Option.Option.None)

def Tests.Rustc_tests__fn_sig_into_try.d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Option.Option i32)
  := do
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  (match (Core.Option.Option.Some (7 : i32)) with
    | (Core.Option.Option.Some _) => do (Core.Option.Option.Some (0 : i32))
    | (Core.Option.Option.None ) => do Core.Option.Option.None)

def Tests.Rustc_tests__fn_sig_into_try.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__fn_sig_into_try.a Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__fn_sig_into_try.b Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__fn_sig_into_try.c Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__fn_sig_into_try.d Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk