
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

inductive Tests.Legacy__pattern_or.E : Type
| A : Tests.Legacy__pattern_or.E 
| B : Tests.Legacy__pattern_or.E 


def Tests.Legacy__pattern_or.E
  (x : Tests.Legacy__pattern_or.E)
  : Result isize
  := do
  (match x with
    | (Tests.Legacy__pattern_or.E.A ) => do (0 : isize)
    | (Tests.Legacy__pattern_or.E.B ) => do (1 : isize))

def Tests.Legacy__pattern_or.bar
  (x : Tests.Legacy__pattern_or.E)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (match x with
    | (Tests.Legacy__pattern_or.E.A ) | (Tests.Legacy__pattern_or.E.B )
      => do Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__pattern_or.nested
  (x : (Core.Option.Option i32))
  : Result i32
  := do
  (match x with
    | (Core.Option.Option.Some TODO_LINE_622) | (Core.Option.Option.Some
        TODO_LINE_622)
      => do (1 : i32)
    | (Core.Option.Option.Some x) => do x
    | (Core.Option.Option.None ) => do (0 : i32))

def Tests.Legacy__pattern_or.deep
  (x : (Rust_primitives.Hax.Tuple2 i32 (Core.Option.Option i32)))
  : Result i32
  := do
  (match x with
    | ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩ | ⟨TODO_LINE_622,
                                                                  (Core.Option.Option.Some
                                                                    TODO_LINE_622)⟩
      | ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩ |
      ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩
      => do (0 : i32)
    | ⟨x, _⟩ => do x)

def Tests.Legacy__pattern_or.equivalent
  (x : (Rust_primitives.Hax.Tuple2 i32 (Core.Option.Option i32)))
  : Result i32
  := do
  (match x with
    | ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩ | ⟨TODO_LINE_622,
                                                                  (Core.Option.Option.Some
                                                                    TODO_LINE_622)⟩
      | ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩ |
      ⟨TODO_LINE_622, (Core.Option.Option.Some TODO_LINE_622)⟩
      => do (0 : i32)
    | ⟨x, _⟩ => do x)

def Tests.Legacy__pattern_or.deep_capture
  (x :
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2 i32 i32)
    (Rust_primitives.Hax.Tuple2 i32 i32)))
  : Result i32
  := do
  (match x with
    | (Core.Result.Result.Ok ⟨TODO_LINE_622, x⟩) | (Core.Result.Result.Ok
        ⟨TODO_LINE_622, x⟩) | (Core.Result.Result.Err ⟨TODO_LINE_622, x⟩) |
      (Core.Result.Result.Err ⟨TODO_LINE_622, x⟩)
      => do x
    | (Core.Result.Result.Ok ⟨x, _⟩) | (Core.Result.Result.Err ⟨x, _⟩) => do x)