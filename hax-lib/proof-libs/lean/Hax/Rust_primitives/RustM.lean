import Hax.Tactic.Init
import Hax.MissingLean.Init.While
import Std.Tactic.Do

open Std.Do
open Std.Tactic

/-
# Monadic encoding

The encoding is based on the `RustM` monad: all rust computations are wrapped
in the monad, representing the fact that they are not total.

It borrows some definitions from the Aeneas project
(https://github.com/AeneasVerif/aeneas/)

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
deriving Repr, BEq, DecidableEq
open Error

/--
  RustM monad (corresponding to Aeneas's `Result` monad), representing
  possible results of rust computations
-/
inductive RustM.{u} (α : Type u) where
  | ok (v: α): RustM α
  | fail (e: Error): RustM α
  | div
deriving Repr, BEq, DecidableEq, Inhabited

namespace RustM

@[simp, hax_bv_decide]
instance instPure: Pure RustM where
  pure x := .ok x

@[simp]
def bind {α β : Type} (x: RustM α) (f: α -> RustM β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def ofOption {α} (x:Option α) (e: Error) : RustM α := match x with
  | .some v => pure v
  | .none => .fail e

@[reducible]
def isOk {α : Type} (x: RustM α) : Bool := match x with
| .ok _ => true
| _ => false

@[reducible, hax_bv_decide]
def of_isOk {α : Type} (x: RustM α) (h: RustM.isOk x): α :=
  match x with
  | .ok v => v

@[simp, spec]
def ok_of_isOk {α : Type} (v : α) (h: isOk (ok v)): (ok v).of_isOk h = v := by rfl

@[simp, hax_bv_decide]
instance instMonad : Monad RustM where
  pure := pure
  bind := RustM.bind

@[simp]
instance instLawfulMonad : LawfulMonad RustM where
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
instance instWP : WP RustM (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

@[simp]
instance instWPMonad : WPMonad RustM (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, Pure.pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const, Bind.bind]

@[default_instance]
instance instCoe {α} : Coe α (RustM α) where
  coe x := pure x

@[simp, spec, default_instance]
instance {α} : Coe (RustM (RustM α)) (RustM α) where
  coe x := match x with
  | .ok y => y
  | .fail e => .fail e
  | .div => .div

section Order

open Lean.Order

/- These instances are required to use `partial_fixpoint` in the `RustM` monad. -/

instance {α} : PartialOrder (RustM α) := inferInstanceAs (PartialOrder (FlatOrder RustM.div))

noncomputable instance {α} : CCPO (RustM α) := inferInstanceAs (CCPO (FlatOrder RustM.div))

noncomputable instance : MonoBind RustM where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹RustM _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl

open Lean Order in
/-- `Loop.MonoLoopCombinator` is used to implement while loops in `RustM`: -/
instance {β : Type} (f : Unit → β → RustM (ForInStep β)) : Loop.MonoLoopCombinator f := {
  mono := by
    unfold Loop.loopCombinator
    repeat monotonicity
}

end Order

end RustM
