
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

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__guards.if_let_guard
  (x : (Core.Option.Option (Core.Result.Result i32 i32)))
  : Result i32
  := do
  (match x with
    | (Core.Option.Option.None ) => do (0 : i32)
    | _
      => do
        (match
          (match x with
            | (Core.Option.Option.Some v)
              => do
                (match v with
                  | (Core.Result.Result.Ok y) => do (Core.Option.Option.Some y)
                  | _ => do Core.Option.Option.None)
            | _ => do Core.Option.Option.None)
        with
          | (Core.Option.Option.Some x) => do x
          | (Core.Option.Option.None )
            => do
              (match x with
                | (Core.Option.Option.Some (Core.Result.Result.Err y)) => do y
                | _ => do (1 : i32))))

def Tests.Legacy__guards.equivalent
  (x : (Core.Option.Option (Core.Result.Result i32 i32)))
  : Result i32
  := do
  (match x with
    | (Core.Option.Option.None ) => do (0 : i32)
    | _
      => do
        (match
          (match x with
            | (Core.Option.Option.Some v)
              => do
                (match v with
                  | (Core.Result.Result.Ok y) => do (Core.Option.Option.Some y)
                  | _ => do Core.Option.Option.None)
            | _ => do Core.Option.Option.None)
        with
          | (Core.Option.Option.Some y) => do y
          | (Core.Option.Option.None )
            => do
              (match x with
                | (Core.Option.Option.Some (Core.Result.Result.Err y)) => do y
                | _ => do (1 : i32))))

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__guards.multiple_guards
  (x : (Core.Option.Option (Core.Result.Result i32 i32)))
  : Result i32
  := do
  (match x with
    | (Core.Option.Option.None ) => do (0 : i32)
    | _
      => do
        (match
          (match x with
            | (Core.Option.Option.Some (Core.Result.Result.Ok v))
              => do
                (match (Core.Option.Option.Some (← v +? (1 : i32))) with
                  | (Core.Option.Option.Some sorry)
                    => do (Core.Option.Option.Some (0 : i32))
                  | _ => do Core.Option.Option.None)
            | _ => do Core.Option.Option.None)
        with
          | (Core.Option.Option.Some x) => do x
          | (Core.Option.Option.None )
            => do
              (match
                (match x with
                  | (Core.Option.Option.Some v)
                    => do
                      (match v with
                        | (Core.Result.Result.Ok y)
                          => do (Core.Option.Option.Some y)
                        | _ => do Core.Option.Option.None)
                  | _ => do Core.Option.Option.None)
              with
                | (Core.Option.Option.Some x) => do x
                | (Core.Option.Option.None )
                  => do
                    (match x with
                      | (Core.Option.Option.Some (Core.Result.Result.Err y))
                        => do y
                      | _ => do (1 : i32)))))

--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__guards.if_guard
  (x : (Core.Option.Option i32))
  : Result i32
  := do
  (match
    (match x with
      | (Core.Option.Option.Some v)
        => do
          (match (← Rust_primitives.Hax.Machine_int.gt v (0 : i32)) with
            | sorry => do (Core.Option.Option.Some v)
            | _ => do Core.Option.Option.None)
      | _ => do Core.Option.Option.None)
  with
    | (Core.Option.Option.Some x) => do x
    | (Core.Option.Option.None ) => do (0 : i32))