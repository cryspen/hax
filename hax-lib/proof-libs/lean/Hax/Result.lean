import Std
import Std.Do.Triple
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-
# Monadic encoding

The encoding is based on the `Result` monad: all rust computations are wrapped
in the monad, representing the fact that they are not total.

-/

/--
  (Aeneas) Error cases
-/
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq
open Error

/-- (Aeneas) Result monad, representing possible results of rust computations -/
inductive Result.{u} (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

namespace Result

@[simp]
instance instPure: Pure Result where
  pure x := .ok x

@[simp]
def bind (x: Result α) (f: α -> Result β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def ofOption {α} (x:Option α) (e: Error) : Result α := match x with
  | .some v => pure v
  | .none => .fail e

@[simp]
instance instMonad : Monad Result where
  pure := pure
  bind := Result.bind

@[simp]
instance instLawfulMonad : LawfulMonad Result where
  id_map x := by
    dsimp [id, Functor.map]
    cases x;
    all_goals grind
  map_const := by
    intros α β
    dsimp [Functor.map, Functor.mapConst]
  seqLeft_eq x y := by
    dsimp [Functor.map, SeqLeft.seqLeft, Seq.seq]
    cases x ; all_goals cases y
    all_goals try simp
  seqRight_eq x y := by
    dsimp [Functor.map, SeqRight.seqRight, Seq.seq]
    cases x ; all_goals cases y
    all_goals try simp
  pure_seq g x := by
    dsimp [Functor.map, Seq.seq, pure]
  bind_pure_comp f x := by
    dsimp [Functor.map]
  bind_map f x := by
    dsimp [Functor.map, bind, pure, Seq.seq]
  pure_bind x f := by
    dsimp [pure, bind, pure]
  bind_assoc x f g := by
    dsimp [pure, bind]
    cases x; all_goals simp

@[simp]
instance instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

@[simp]
instance instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, Pure.pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const, Bind.bind]

@[default_instance]
instance instCoe {α} : Coe α (Result α) where
  coe x := pure x

end Result
