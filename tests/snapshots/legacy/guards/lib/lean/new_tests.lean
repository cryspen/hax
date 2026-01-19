
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


namespace new_tests.legacy__guards__lib

--  @fail(extraction): proverif(HAX0008)
def if_let_guard
    (x : (core_models.option.Option (core_models.result.Result i32 i32))) :
    RustM i32 := do
  match x with
    | (core_models.option.Option.None ) => (pure (0 : i32))
    | _ =>
      match
        (← match x with
          | (core_models.option.Option.Some  v) =>
            match v with
              | (core_models.result.Result.Ok  y) =>
                (pure (core_models.option.Option.Some y))
              | _ => (pure core_models.option.Option.None)
          | _ => (pure core_models.option.Option.None))
      with
        | (core_models.option.Option.Some  x) => (pure x)
        | (core_models.option.Option.None ) =>
          match x with
            | (core_models.option.Option.Some
                 (core_models.result.Result.Err  y)) =>
              (pure y)
            | _ => (pure (1 : i32))

def equivalent
    (x : (core_models.option.Option (core_models.result.Result i32 i32))) :
    RustM i32 := do
  match x with
    | (core_models.option.Option.None ) => (pure (0 : i32))
    | _ =>
      match
        (← match x with
          | (core_models.option.Option.Some  v) =>
            match v with
              | (core_models.result.Result.Ok  y) =>
                (pure (core_models.option.Option.Some y))
              | _ => (pure core_models.option.Option.None)
          | _ => (pure core_models.option.Option.None))
      with
        | (core_models.option.Option.Some  y) => (pure y)
        | (core_models.option.Option.None ) =>
          match x with
            | (core_models.option.Option.Some
                 (core_models.result.Result.Err  y)) =>
              (pure y)
            | _ => (pure (1 : i32))

--  @fail(extraction): proverif(HAX0008)
def multiple_guards
    (x : (core_models.option.Option (core_models.result.Result i32 i32))) :
    RustM i32 := do
  match x with
    | (core_models.option.Option.None ) => (pure (0 : i32))
    | _ =>
      match
        (← match x with
          | (core_models.option.Option.Some  (core_models.result.Result.Ok  v))
            =>
            match (core_models.option.Option.Some (← (v +? (1 : i32)))) with
              | (core_models.option.Option.Some  1) =>
                (pure (core_models.option.Option.Some (0 : i32)))
              | _ => (pure core_models.option.Option.None)
          | _ => (pure core_models.option.Option.None))
      with
        | (core_models.option.Option.Some  x) => (pure x)
        | (core_models.option.Option.None ) =>
          match
            (← match x with
              | (core_models.option.Option.Some  v) =>
                match v with
                  | (core_models.result.Result.Ok  y) =>
                    (pure (core_models.option.Option.Some y))
                  | _ => (pure core_models.option.Option.None)
              | _ => (pure core_models.option.Option.None))
          with
            | (core_models.option.Option.Some  x) => (pure x)
            | (core_models.option.Option.None ) =>
              match x with
                | (core_models.option.Option.Some
                     (core_models.result.Result.Err  y)) =>
                  (pure y)
                | _ => (pure (1 : i32))

--  @fail(extraction): proverif(HAX0008)
def if_guard (x : (core_models.option.Option i32)) : RustM i32 := do
  match
    (← match x with
      | (core_models.option.Option.Some  v) =>
        match (← (rust_primitives.hax.machine_int.gt v (0 : i32))) with
          | true => (pure (core_models.option.Option.Some v))
          | _ => (pure core_models.option.Option.None)
      | _ => (pure core_models.option.Option.None))
  with
    | (core_models.option.Option.Some  x) => (pure x)
    | (core_models.option.Option.None ) => (pure (0 : i32))

end new_tests.legacy__guards__lib

