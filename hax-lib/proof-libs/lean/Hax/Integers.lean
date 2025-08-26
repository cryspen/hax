import Hax.Integers.Basic
import Hax.Integers.Arithmetic
import Hax.Integers.Int32
import Hax.BitVec

open Error
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-

# Properties

For each integer types, instances of typeclasses for arithmetic operations are
given, along with hoare-triple specifications (to be used by mvcgen)

-/

namespace USize

/-- Partial addition on usize -/
instance instHaxAdd : HaxAdd USize where
  add x y :=
    if (BitVec.uaddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

/-- Partial substraction on usize -/
instance instHaxSub : HaxSub USize where
  sub x y :=
    if (BitVec.usubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

/-- Partial multiplication on usize -/
instance instHaxMul : HaxMul USize where
  mul x y :=
    if (BitVec.umulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

/-- Partial right shift on usize -/
instance instHaxShiftRight : HaxShiftRight USize where
  shiftRight x y :=
    if (y ≤ USize.size) then pure (x >>> y)
    else .fail .integerOverflow

/-- Partial division on usize. As it is unsigned, it only checks that the
divider is non-zero. -/
instance instHaxDiv : HaxDiv usize where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x / y)

/-- Partial remainder on usize. As it is unsigned, it only checks that the
divider is non zero -/
instance instHaxRem : HaxRem usize where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x % y)

/- # Bitvec specifications -/

/-- Bitvec-based specification for rust addition on usize -/
theorem HaxAdd_spec_bv (x y: usize) :
  ¬ (BitVec.uaddOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by intros; mvcgen [instHaxAdd]

/-- Bitvec-based specification for rust multiplication on usize -/
theorem HaxMul_spec_bv (x y: usize) :
  ¬ (BitVec.umulOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by intros; mvcgen [instHaxMul]

/-- Bitvec-based specification for rust substraction on usize -/
@[spec]
theorem HaxSub_spec_bv (x y: usize) :
  ¬ (BitVec.usubOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by intros; mvcgen [instHaxSub]

/-- Bitvec-based specification for rust right-shift on usize -/
@[spec]
theorem HaxShiftRight_spec_bv (x y: usize) :
  y ≤ USize.size →
  ⦃ ⌜ True ⌝ ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by intros; mvcgen [instHaxShiftRight]

/-- Bitvec-based specification for rust division on usize -/
@[spec]
theorem HaxDiv_spec_bv (x y : usize) :
  y != 0 →
  ⦃ ⌜ True ⌝ ⦄
  ( x /? y)
  ⦃ ⇓ r => r = x / y ⦄
:= by intros; mvcgen [instHaxDiv] <;> simp <;> try grind

/-- Bitvec-based specification for rust remainder on usize  -/
@[spec]
theorem HaxRem_spec_bv (x y : usize) :
  y != 0 →
  ⦃ ⌜ True ⌝ ⦄
  ( x %? y)
  ⦃ ⇓ r => r = x % y ⦄
:= by intros; mvcgen [instHaxRem] <;> simp <;> try grind


/- # Nat specifications -/

/-- Nat-based specification for rust addition on usize -/
theorem HaxAdd_spec_nat (x y: usize) :
  x.toNat + y.toNat < size →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by
  intros
  mvcgen [HaxAdd_spec_bv] ; simp
  apply eq_false_of_ne_true
  apply BitVec.toNat_add_iff_not_uaddOverflow.mp
  simp [USize.toNat_toBitVec, size, Nat.mod_eq_iff_lt] at *; assumption

/-- Nat-based specification for rust multiplication on usize -/
theorem HaxMul_spec_nat (x y: usize) :
  x.toNat * y.toNat < size →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by
  intros
  mvcgen [HaxMul_spec_bv] ; simp
  apply eq_false_of_ne_true
  apply BitVec.toNat_mul_iff_not_umulOverflow.mp
  simp [USize.toNat_toBitVec, size, Nat.mod_eq_iff_lt] at *; assumption

end USize

namespace SpecNat
attribute [scoped spec]
  USize.HaxAdd_spec_nat
  USize.HaxMul_spec_nat
end SpecNat

namespace SpecBV
attribute [scoped spec]
  USize.HaxAdd_spec_bv
  USize.HaxSub_spec_bv
  USize.HaxMul_spec_bv
  USize.HaxDiv_spec_bv
  USize.HaxRem_spec_bv
  USize.HaxShiftRight_spec_bv
end SpecBV


namespace ISize

instance instHaxAdd : HaxAdd ISize where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

@[spec]
theorem HaxAdd_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd]

theorem HaxAdd_spec_bv_rw (x y: isize) :
   ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
   x +? y = Result.ok (x + y)
:= by simp [instHaxAdd]


instance instHaxSub : HaxSub ISize where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

instance instHaxMul : HaxMul ISize where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

@[spec]
theorem HaxMul_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by mvcgen [instHaxMul]

instance instHaxShiftRight : HaxShiftRight ISize where
  shiftRight x y :=
    if (y ≤ ISize.size.toISize) then pure (x >>> y)
    else .fail .integerOverflow

@[spec]
theorem HaxShiftRight_spec_bv (x y: isize) :
  ⦃ y ≤ ISize.size.toISize ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by mvcgen [instHaxShiftRight]

end ISize


namespace Int64

/-- Partial addition on i64 -/
instance instHaxAdd : HaxAdd Int64 where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

/-- Partial substraction on i64 -/
instance instHaxSub : HaxSub Int64 where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

/-- Partial multiplication on i64 -/
instance instHaxMul : HaxMul Int64 where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

/-- Partial division on i64 -/
instance instHaxDiv : HaxDiv Int64 where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x / y)

/-- Partial right shift on i64 -/
instance instHaxShiftRight : HaxShiftRight Int64 where
  shiftRight x y :=
    if (y ≤ 64) then pure (x >>> y)
    else .fail .integerOverflow

variable (x y :i64)
abbrev max := Int64.maxValue.toInt
abbrev min := Int64.minValue.toInt

/- # Bitvec specifications -/

/-- Bitvec-based specification for addition on i64 -/
theorem HaxAdd_spec_bv :
  ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x +? y) ⦃ ⇓ r => r = x + y ⦄ :=
  by intros; mvcgen [instHaxAdd]

/-- Bitvec-based specification for substraction on i64 -/
theorem HaxSub_spec_bv :
  ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x -? y) ⦃ ⇓ r => r = x - y ⦄ :=
  by intros; mvcgen [instHaxSub]

/-- Bitvec-based specification for multiplication on i64 -/
theorem HaxMul_spec_bv :
  ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x *? y) ⦃ ⇓ r => r = x * y ⦄ :=
  by intros; mvcgen [instHaxMul]

/-- Bitvec-based specification for division on i64 -/
theorem HaxDiv_spec_bv :
  y ≠ 0 →
  ¬ (BitVec.sdivOverflow x.toBitVec y.toBitVec) →
  ⦃ True ⦄ (x /? y) ⦃ ⇓ r => r = x / y ⦄ :=
  by intros; mvcgen [instHaxDiv]

/-- Bitvec-based specification for division on i64 -/
theorem HaxShiftRight_spec_bv :
  y ≤ 64 →
  ⦃ True ⦄ (x >>>? y) ⦃ ⇓ r => r = x >>> y ⦄ :=
  by intros; mvcgen [instHaxShiftRight]

/- # Int specifications -/

/-- Int-based specification for rust addition on i64 -/
theorem HaxAdd_spec_int :
  x.toInt + y.toInt ≤ max →
  min ≤ x.toInt + y.toInt →
  ⦃ True ⦄ (x +? y) ⦃⇓ r => r = x + y ⦄ :=
  by sorry

/-- Int-based specification for rust multiplication on i64 -/
theorem HaxMul_spec_int :
  x.toInt * y.toInt < size →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ :=
  by sorry

/-- Int-based specification for division on i64 -/
theorem HaxShiftRight_spec_int :
  y.toInt ≤ 64 →
  ⦃ True ⦄ (x >>>? y) ⦃ ⇓ r => r = x >>> y ⦄ :=
  by
  intros
  mvcgen [instHaxShiftRight]
  simp [Int64.le_iff_toInt_le] at *
  omega

end Int64

namespace SpecNat
attribute [scoped spec]
  Int64.HaxAdd_spec_int
  Int64.HaxMul_spec_int
  Int64.HaxShiftRight_spec_int
end SpecNat

namespace SpecBV
attribute [scoped spec]
  Int64.HaxAdd_spec_bv
  Int64.HaxSub_spec_bv
  Int64.HaxMul_spec_bv
  Int64.HaxDiv_spec_bv
  Int64.HaxShiftRight_spec_bv
end SpecBV
