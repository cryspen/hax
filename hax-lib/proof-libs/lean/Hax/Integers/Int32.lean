import Hax.Integers.Basic
import Hax.Integers.Arithmetic
import Hax.Result
open Std.Do
open Std.Tactic
set_option mvcgen.warning false


namespace Int32

/-- Partial addition on i32 -/
instance instHaxAdd : HaxAdd Int32 where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

/-- Partial substraction on i32 -/
instance instHaxSub : HaxSub Int32 where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

/-- Partial multiplication on i32 -/
instance instHaxMul : HaxMul Int32 where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

/-- Partial remainder on i32 -/
instance instHaxDiv : HaxDiv Int32 where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x / y)

/-- Partial remainder on i32 -/
instance instHaxRem : HaxRem Int32 where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x % y)

end Int32

namespace Spec
open Int32

variable (x y :i32)
abbrev max := maxValue.toInt
abbrev min := minValue.toInt

attribute [scoped simp, spec]
  max
  maxValue
  instHaxAdd
  instHaxSub
  instHaxMul
  instHaxDiv
  instHaxRem
  BitVec.saddOverflow
  BitVec.ssubOverflow
  BitVec.smulOverflow
  BitVec.sdivOverflow


/- # Bitvec specifications -/
namespace BitVec.Int32

/-- Bitvec-based specification for addition on i32 -/
theorem HaxAdd :
  ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x +? y) ⦃ ⇓ r => r = x + y ⦄ :=
  by intros; mvcgen

/-- Bitvec-based specification for substraction on i32 -/
theorem HaxSub :
  ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x -? y) ⦃ ⇓ r => r = x - y ⦄ :=
  by intros; mvcgen

/-- Bitvec-based specification for multiplication on i32 -/
theorem HaxMul :
  ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x *? y) ⦃ ⇓ r => r = x * y ⦄ :=
  by intros; mvcgen

/-- Bitvec-based specification for division on i32 -/
theorem HaxDiv :
  y ≠ 0 →
  ¬ (BitVec.sdivOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x /? y) ⦃ ⇓ r => r = x / y ⦄ :=
  by intros; mvcgen

/-- Bitvec-based specification for remainder on i32 -/
theorem HaxRem :
  y ≠ 0 →
  ¬ (BitVec.sdivOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x %? y) ⦃ ⇓ r => r = x % y ⦄ :=
  by intros; mvcgen

end BitVec.Int32



/- # Int specifications -/
namespace IntNat.Int32

/-- Int-based specification for rust addition on i32 -/
theorem HaxAdd :
  x.toInt + y.toInt ≤ max →
  min ≤ x.toInt + y.toInt →
  ⦃ True ⦄ (x +? y) ⦃⇓ r => r = x + y ⦄ :=
  by intros; mvcgen ; simp at * ; omega

/-- Int-based specification for rust substraction on i32 -/
theorem HaxSub :
  x.toInt - y.toInt ≤ max →
  min ≤ x.toInt - y.toInt →
  ⦃ True ⦄ (x -? y) ⦃⇓ r => r = x - y ⦄ :=
  by intros; mvcgen ; simp at * ; omega

/-- Int-based specification for rust multiplication on i32 -/
theorem HaxMul :
  x.toInt * y.toInt ≤ max →
  min ≤ x.toInt * y.toInt →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ :=
  by intros; mvcgen ; simp at * ; omega

/-- Int-based specification for rust multiplication on i32 -/
theorem HaxDiv :
  y.toInt ≠ 0 →
  ¬(y.toInt = -1 ∧ x.toInt = max) →
  ⦃ ⌜ True ⌝ ⦄
  (x /? y)
  ⦃ ⇓ r => r = x / y ⦄ :=
  by sorry

/-- Int-based specification for rust multiplication on i32 -/
theorem HaxRem :
  x.toInt * y.toInt ≤ max →
  min ≤ x.toInt * y.toInt →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ :=
  by sorry

end IntNat.Int32

/- Manual rewrites -/

-- theorem HaxAdd_spec_bv_rw :
--   ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
--   x +? y = Result.ok (x + y) := by simp [instHaxAdd ] <;> grind

-- theorem HaxSub_spec_bv_rw (x y: i32) :
--   ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) →
--   x -? y = Result.ok (x - y) := by simp [instHaxSub ] <;> grind

-- theorem HaxRem_spec_bv_rw (x y : i32) :
--   y != 0 →
--   ¬ BitVec.sdivOverflow x.toBitVec y.toBitVec →
--   x %? y = Result.ok (x % y) := by simp [instHaxRem] <;> try grind

end Spec



namespace Spec.IntNat
attribute [scoped spec]
  Int32.HaxAdd
  Int32.HaxSub
  Int32.HaxMul
  Int32.HaxDiv
  Int32.HaxRem
end Spec.IntNat

namespace SpecBV
attribute [scoped spec]
  Int32.HaxAdd_spec_bv
  Int32.HaxSub_spec_bv
  Int32.HaxMul_spec_bv
  Int32.HaxDiv_spec_bv
  Int32.HaxRem_spec_bv
end SpecBV
