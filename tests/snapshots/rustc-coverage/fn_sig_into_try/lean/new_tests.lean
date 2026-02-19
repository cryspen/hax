
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


namespace new_tests.rustc_coverage__fn_sig_into_try

def a (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.option.Option i32) := do
  let _ := (core_models.option.Option.Some (7 : i32));
  (pure (core_models.option.Option.Some (0 : i32)))

def b (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.option.Option i32) := do
  match (core_models.option.Option.Some (7 : i32)) with
    | (core_models.option.Option.Some  _) =>
      (pure (core_models.option.Option.Some (0 : i32)))
    | (core_models.option.Option.None ) => (pure core_models.option.Option.None)

def c (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.option.Option i32) := do
  match (core_models.option.Option.Some (7 : i32)) with
    | (core_models.option.Option.Some  _) =>
      (pure (core_models.option.Option.Some (0 : i32)))
    | (core_models.option.Option.None ) => (pure core_models.option.Option.None)

def d (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.option.Option i32) := do
  let _ : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk;
  match (core_models.option.Option.Some (7 : i32)) with
    | (core_models.option.Option.Some  _) =>
      (pure (core_models.option.Option.Some (0 : i32)))
    | (core_models.option.Option.None ) => (pure core_models.option.Option.None)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (a rust_primitives.hax.Tuple0.mk);
  let _ ← (b rust_primitives.hax.Tuple0.mk);
  let _ ← (c rust_primitives.hax.Tuple0.mk);
  let _ ← (d rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__fn_sig_into_try

