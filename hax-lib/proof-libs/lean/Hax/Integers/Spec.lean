/-
Hax Lean Backend - Cryspen

Specifications for integer operations
-/

import Hax.Lib
import Hax.Integers.Ops
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace UnSigned.Spec.BV

/-- Bitvec-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [UnSigned α] (x y : α):
  ¬ (BitVec.uaddOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by intros; mvcgen [instHaxAddOfUnSigned]

/-- Bitvec-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [UnSigned α] (x y : α):
  ¬ (BitVec.usubOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by intros; mvcgen [instHaxSubOfUnSigned]

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [UnSigned α] (x y : α):
  ¬ (BitVec.umulOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by intros; mvcgen [instHaxMulOfUnSigned]

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxDiv {α : Type} [UnSigned α] (x y : α):
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
  := by intros; mvcgen [instHaxDivOfUnSigned]

/-- Bitvec-based specification for rust remainder on signed integers -/
theorem HaxRem {α : Type} [UnSigned α] (x y : α):
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
  := by intros; mvcgen [instHaxRemOfUnSigned]

/-- Bitvec-based specification for rust remainder on signed integers -/
theorem HaxShiftRight {α : Type} [UnSigned α] (x y : α):
  (UnSigned.toNat y) < (UnSigned.width α) →
  ⦃ ⌜ True ⌝ ⦄ (x >>>? y) ⦃ ⇓ r => ⌜ r = x >>> y ⌝ ⦄
  := by intros; mvcgen [instHaxShiftRightOfUnSigned] ; omega

end UnSigned.Spec.BV


namespace Signed.Spec.BV

/-- Bitvec-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.saddOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by intros; mvcgen [instHaxAddOfSigned]

/-- Bitvec-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.ssubOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by intros; mvcgen [instHaxSubOfSigned]

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.smulOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by intros; mvcgen [instHaxMulOfSigned]

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxDiv {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
  := by intros; mvcgen [instHaxDivOfSigned]

/-- Bitvec-based specification for rust remainder on signed integers -/
theorem HaxRem {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
  := by intros; mvcgen [instHaxRemOfSigned]

/-- Bitvec-based specification for rust right-shift on signed integers -/
theorem HaxShiftRight {α : Type} [Signed α] (x y : α):
  0 ≤ (Signed.toInt y) →
  (Signed.toInt y) < Int.ofNat (Signed.width α) →
  ⦃ ⌜ True ⌝ ⦄ (x >>>? y) ⦃ ⇓ r => ⌜ r = x >>> y ⌝ ⦄
  := by intros; mvcgen [instHaxShiftRightOfSigned] ; simp at * ; omega

end Signed.Spec.BV



namespace Signed.Spec.Nat

/-- Bitvec-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) + (Signed.toInt y) →
  (Signed.toInt x) + (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by
  intros; mvcgen [instHaxAddOfSigned, BitVec.saddOverflow, Signed]
  simp [Signed.toInt_toBitVec] at *; omega


/-- Bitvec-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) - (Signed.toInt y) →
  (Signed.toInt x) - (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by
  intros; mvcgen [instHaxSubOfSigned, BitVec.ssubOverflow]
  simp [Signed.toInt_toBitVec] at *; omega

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) * (Signed.toInt y) →
  (Signed.toInt x) * (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by
  intros; mvcgen [instHaxMulOfSigned, BitVec.smulOverflow]
  simp [Signed.toInt_toBitVec] at *; omega

end Signed.Spec.Nat


-- Registering instances for mvcgen
namespace Spec.BV
attribute [scoped spec]
  Signed.Spec.BV.HaxAdd
  Signed.Spec.BV.HaxSub
  Signed.Spec.BV.HaxMul
  Signed.Spec.BV.HaxDiv
  Signed.Spec.BV.HaxRem
  Signed.Spec.BV.HaxShiftRight

  UnSigned.Spec.BV.HaxAdd
  UnSigned.Spec.BV.HaxSub
  UnSigned.Spec.BV.HaxMul
  UnSigned.Spec.BV.HaxDiv
  UnSigned.Spec.BV.HaxRem
  UnSigned.Spec.BV.HaxShiftRight
end Spec.BV

-- Registering instances for mvcgen
namespace Spec.Nat
attribute [scoped spec]
  Signed.Spec.Nat.HaxAdd
  Signed.Spec.Nat.HaxSub
  Signed.Spec.Nat.HaxMul
end Spec.Nat
