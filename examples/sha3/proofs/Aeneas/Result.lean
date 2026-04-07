import Std

namespace Aeneas
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
deriving Repr, BEq, DecidableEq
open Error

/--
  RustM monad (corresponding to Aeneas's `Result` monad), representing
  possible results of rust computations.

  Defined as `ExceptT Error Option`, i.e. `Option (Except Error α)`.
  The `Option` layer models divergence and the `Except Error` layer models
  Rust panics. The `ExceptT` transformer ensures that once a program has
  paniced, it can not diverge any more (and vice versa).
-/
def Result (α : Type) := ExceptT Error Option α

namespace Result

-- These `Except` instances are missing in Lean's library.
-- We use them to derive the corresponding `Result` instances below.
deriving instance BEq, DecidableEq for Except

instance instBEq {α : Type} [BEq α] : BEq (Result α) :=
  inferInstanceAs (BEq (Option (Except Error α)))
instance instDecidableEq {α : Type} [DecidableEq α] : DecidableEq (Result α) :=
  inferInstanceAs (DecidableEq (Option (Except Error α)))
instance instInhabited {α : Type} : Inhabited (Result α) :=
  inferInstanceAs (Inhabited (Option (Except Error α)))
instance instMonad : Monad Result :=
  inferInstanceAs (Monad (ExceptT Error Option))
instance instLawfulMonad : LawfulMonad Result :=
  inferInstanceAs (LawfulMonad (ExceptT Error Option))

@[reducible, match_pattern] def ok {α : Type} (v : α) : Result α := some (.ok v)
@[reducible, match_pattern] def fail {α : Type} (e : Error) : Result α := some (.error e)
@[reducible, match_pattern] def div {α : Type} : Result α := none

instance {α : Type} [Repr α] : Repr (Result α) where
  reprPrec x prec := match x with
    | .ok v   => Repr.addAppParen (f!"Result.ok {reprArg v}") prec
    | .fail e => Repr.addAppParen (f!"Result.fail {reprArg e}") prec
    | .div    => "Result.div"

def ofOption {α : Type} (x : Option α) (e : Error) : Result α :=
  match x with
  | .some v => pure v
  | .none => .fail e

@[reducible]
def isOk {α : Type} (x : Result α) : Bool :=
  match x with
  | .ok _ => true
  | _ => false

@[reducible]
def of_isOk {α : Type} (x : Result α) (h : Result.isOk x) : α :=
  match x with
  | .ok v => v

@[simp, spec]
def ok_of_isOk {α : Type} (v : α) (h : isOk (ok v)) : (ok v).of_isOk h = v := by rfl

open Std.Do

instance instWP : WP Result (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WP (ExceptT Error Option) _)
instance instWPMonad : WPMonad Result (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WPMonad (ExceptT Error Option) _)

abbrev holds (x : Result Prop) : Prop := ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ p => ⌜ p ⌝ ⦄

def lift {α : Type} (x : α) : Result α := .ok x
