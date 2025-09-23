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


namespace UnSigned.Spec

attribute [scoped simp, scoped spec]
  BitVec.uaddOverflow
  BitVec.usubOverflow
  BitVec.umulOverflow
  instHaxAddOfUnSigned
  instHaxSubOfUnSigned
  instHaxMulOfUnSigned
  instHaxDivOfUnSigned
  instHaxRemOfUnSigned
  instHaxShiftRightOfUnSigned

attribute [scoped simp]
  UnSigned.toNat_toBitVec

namespace BV

/-- Bitvec-based specification for rust addition on unsigned integers -/
theorem HaxAdd {α : Type} [i: UnSigned α] (x y : α):
  ¬ (BitVec.uaddOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust subtraction on unsigned integers -/
theorem HaxSub {α : Type} [UnSigned α] (x y : α):
  ¬ (BitVec.usubOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust multiplication on unsigned integers -/
theorem HaxMul {α : Type} [i: UnSigned α] (x y : α):
  ¬ (BitVec.umulOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust multiplication on unsigned integers -/
theorem HaxDiv {α : Type} [UnSigned α] (x y : α):
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust remainder on unsigned integers -/
theorem HaxRem {α : Type} [UnSigned α] (x y : α):
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust remainder on unsigned integers -/
theorem HaxShiftRight {α : Type} [UnSigned α] (x y : α):
  (UnSigned.toNat y) < (width α) →
  ⦃ ⌜ True ⌝ ⦄ (x >>>? y) ⦃ ⇓ r => ⌜ r = x >>> y ⌝ ⦄
  := by intros; mvcgen ; omega

end BV


namespace BV_post

/-- Bitvec-based specification for rust addition on unsigned integers,
    with no overflow in post-condition -/
theorem HaxAdd {α : Type} [i: UnSigned α] (x y : α):
  ¬ (BitVec.uaddOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => ⌜
    r = x + y ∧
    (UnSigned.toNat x) + (UnSigned.toNat y) < 2 ^ (i.width) ⌝ ⦄
  := by intros; mvcgen ; simp at * ; assumption

/-- Bitvec-based specification for rust subtraction on unsigned integers
    with no overflow in post-condition -/
theorem HaxSub {α : Type} [i: UnSigned α] (x y : α):
  ¬ (BitVec.usubOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x -? y)
  ⦃ ⇓ r =>
    ⌜ r = x - y ∧
      0 ≤ (UnSigned.toNat x) - (UnSigned.toNat y) ⌝ ⦄
  := by intros; mvcgen ; simp at *

/-- Bitvec-based specification for rust multiplication on unsigned integers
    with no overflow in post-condition -/
theorem HaxMul {α : Type} [i: UnSigned α] (x y : α):
  ¬ (BitVec.umulOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => ⌜
    r = x * y ∧
    (i.toNat x) * (i.toNat y) < 2 ^ i.width ⌝ ⦄
  := by intros; mvcgen ; simp at * ; assumption



end BV_post


namespace Nat

/-- Nat-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [UnSigned α] (x y : α):
  (toNat x) + (toNat y) < 2^(width α) →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega


/-- Nat-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [UnSigned α] (x y : α):
  (toNat y) ≤ (toNat x) →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega

/-- Nat-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [UnSigned α] (x y : α):
  (toNat x) * (toNat y) < 2^(width α)→
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega

/-- Nat-based specification for rust division on signed integers -/
theorem HaxDiv {α : Type} [UnSigned α] (x y : α):
  y ≠ 0 →
  ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
  := by intros; mvcgen

/-- Nat-based specification for rust remainder on signed integers -/
theorem HaxRem {α : Type} [UnSigned α] (x y : α):
  y ≠ 0 →
  ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
  := by intros; mvcgen

end Nat


end UnSigned.Spec



namespace Signed.Spec

attribute [scoped simp, scoped spec]
  BitVec.saddOverflow
  BitVec.ssubOverflow
  BitVec.smulOverflow
  BitVec.sdivOverflow
  instHaxAddOfSigned
  instHaxSubOfSigned
  instHaxMulOfSigned
  instHaxDivOfSigned
  instHaxRemOfSigned
  instHaxShiftRightOfSigned

attribute [scoped simp]
  Signed.toInt_toBitVec

namespace BV

/-- Bitvec-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.saddOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.ssubOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.smulOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxDiv {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust remainder on signed integers -/
theorem HaxRem {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y)) →
  ¬ y = 0 →
  ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
  := by intros; mvcgen

/-- Bitvec-based specification for rust right-shift on signed integers -/
theorem HaxShiftRight {α : Type} [Signed α] (x y : α):
  0 ≤ (Signed.toInt y) →
  (Signed.toInt y) < Int.ofNat (Signed.width α) →
  ⦃ ⌜ True ⌝ ⦄ (x >>>? y) ⦃ ⇓ r => ⌜ r = x >>> y ⌝ ⦄
  := by intros; mvcgen; simp at * ; omega

end BV


namespace BV_post

/-- Bitvec-based specification for rust addition on signed integers,
    with no overflow in post-condition -/
theorem HaxAdd {α : Type} [Signed α] (x y : α):
  ¬ (BitVec.saddOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => ⌜
    r = x + y ∧
    - 2 ^ (width α - 1) ≤ (toInt x) + (toInt y) ∧
    (toInt x) + (toInt y) ≤ 2 ^ (width α - 1) ⌝ ⦄
  := by intros; mvcgen; simp at * ; omega


/-- Bitvec-based specification for rust subtraction on signed integers
    with no overflow in post-condition -/
theorem HaxSub {α : Type} [i: Signed α] (x y : α):
  ¬ (BitVec.ssubOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x -? y)
  ⦃ ⇓ r => ⌜
    r = x - y ∧
    - 2 ^ (width α - 1) ≤ (toInt x) - (toInt y) ∧
    (toInt x) - (toInt y) ≤ 2 ^ (width α - 1) ⌝ ⦄
  := by intros; mvcgen; simp at * ; omega

/-- Bitvec-based specification for rust multiplication on signed integers
    with no overflow in post-condition -/
theorem HaxMul {α : Type} [i: Signed α] (x y : α):
  ¬ (BitVec.smulOverflow (toBitVec x) (toBitVec y)) →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => ⌜
    r = x * y ∧
    - 2 ^ (width α - 1) ≤ (toInt x) * (toInt y) ∧
    (toInt x) * (toInt y) ≤ 2 ^ (width α - 1) ⌝ ⦄
  := by intros; mvcgen; simp at * ; omega

end BV_post


namespace Nat

/-- Bitvec-based specification for rust addition on signed integers -/
theorem HaxAdd {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) + (Signed.toInt y) →
  (Signed.toInt x) + (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega


/-- Bitvec-based specification for rust subtraction on signed integers -/
theorem HaxSub {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) - (Signed.toInt y) →
  (Signed.toInt x) - (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega

/-- Bitvec-based specification for rust multiplication on signed integers -/
theorem HaxMul {α : Type} [Signed α] (x y : α):
  -2^(Signed.width (α := α) - 1) ≤ (Signed.toInt x) * (Signed.toInt y) →
  (Signed.toInt x) * (Signed.toInt y) ≤ 2^(Signed.width (α := α) - 1) - 1 →
  ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
  := by
  intros; mvcgen ; simp at *; omega

end Nat

end Signed.Spec


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
namespace Spec.BV_post
attribute [scoped spec]
  UnSigned.Spec.BV_post.HaxAdd
  UnSigned.Spec.BV_post.HaxSub
  UnSigned.Spec.BV_post.HaxMul

  Signed.Spec.BV_post.HaxAdd
  Signed.Spec.BV_post.HaxSub
  Signed.Spec.BV_post.HaxMul

  open Spec.BV
end Spec.BV_post


-- Registering instances for mvcgen
namespace Spec.Nat
attribute [scoped spec]
  UnSigned.Spec.Nat.HaxAdd
  UnSigned.Spec.Nat.HaxSub
  UnSigned.Spec.Nat.HaxMul
  UnSigned.Spec.Nat.HaxRem
  UnSigned.Spec.Nat.HaxDiv

  Signed.Spec.Nat.HaxAdd
  Signed.Spec.Nat.HaxSub
  Signed.Spec.Nat.HaxMul
end Spec.Nat
