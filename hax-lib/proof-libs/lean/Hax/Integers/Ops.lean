/-
Hax Lean Backend - Cryspen

Support for integer operations
-/

import Hax.Lib
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


/-

# Arithmetic operations

The Rust arithmetic operations have their own notations, using a `?`. They
return a `Result`, that is `.fail` when arithmetic overflows occur.

-/

/-- The notation typeclass for homogeneous addition that returns a Result.  This
enables the notation `a +? b : α` where `a : α`, `b : α`. For now, there is no
heterogeneous version -/
class HaxAdd α where
  /-- `a +? b` computes the panicking sum of `a` and `b`.  The meaning of this
  notation is type-dependent. -/
  add : α → α → Result α

/-- The notation typeclass for homogeneous substraction that returns a Result.
This enables the notation `a -? b : α` where `a : α`, `b : α`. For now, there is
no heterogeneous version -/
class HaxSub α where
  /-- `a -? b` computes the panicking substraction of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  sub : α → α → Result α

/-- The notation typeclass for homogeneous multiplication that returns a Result.
This enables the notation `a *? b : Result α` where `a b : α`. For now, there is
no heterogeneous version -/
class HaxMul α where
  /-- `a -? b` computes the panicking multiplication of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  mul : α → α → Result α

/-- The notation typeclass for homogeneous division that returns a Result.  This
enables the notation `a /? b : Result α` where `a b : α`. For now, there is no
heterogeneous version -/
class HaxDiv α where
  /-- `a -? b` computes the panicking multiplication of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  div : α → α → Result α

/--The notation typeclass for right shift that returns a Result. It enables the
 notation `a >>>? b : Result α` where `a : α` and `b : β`. -/
class HaxShiftRight α β where
  /-- `a >>>? b` computes the panicking right-shift of `a` by `b`.  The meaning
  of this notation is type-dependent. It panics if `b` exceeds the size of `a`.
  -/
  shiftRight : α → β → Result α

/-- The notation typeclass for remainder.  This enables the notation `a %? b :
Result α` where `a b : α`.  -/
class HaxRem α where
  /-- `a %? b` computes the panicking remainder upon dividing `a` by `b`.  The
  meaning of this notation is type-dependent. It panics if b is zero -/
  rem : α → α → Result α

@[inherit_doc] infixl:65 " +? "   => HaxAdd.add
@[inherit_doc] infixl:65 " -? "   => HaxSub.sub
@[inherit_doc] infixl:70 " *? "   => HaxMul.mul
@[inherit_doc] infixl:75 " >>>? " => HaxShiftRight.shiftRight
@[inherit_doc] infixl:70 " %? "   => HaxRem.rem
@[inherit_doc] infixl:70 " /? "   => HaxDiv.div


/- UnSigned operations -/
class UnSigned (α: Type)
  extends (LE α),
          (OfNat α 0),
          (Add α),
          (Sub α),
          (Mul α),
          (Div α),
          (Mod α),
          (ShiftRight α)
  where
  [deq : DecidableEq α]
  width    : Nat
  size     : Nat
  toBitVec : α → BitVec width
  toNat    : α → Nat
  toNat_toBitVec : (x: α) -> (toBitVec x).toNat = (toNat x)
instance {α : Type} [i: UnSigned α] : DecidableEq α := i.deq

@[simp, reducible]
instance : UnSigned u8 where
  width    := 8
  size     := UInt8.size
  toBitVec := UInt8.toBitVec
  toNat    := UInt8.toNat
  toNat_toBitVec := UInt8.toNat_toBitVec

@[simp, reducible]
instance : UnSigned u16 where
  width    := 16
  size     := UInt16.size
  toBitVec := UInt16.toBitVec
  toNat    := UInt16.toNat
  toNat_toBitVec := UInt16.toNat_toBitVec

@[simp, reducible]
instance : UnSigned u32 where
  width    := 32
  size     := UInt32.size
  toBitVec := UInt32.toBitVec
  toNat    := UInt32.toNat
  toNat_toBitVec := UInt32.toNat_toBitVec

@[simp, reducible]
instance : UnSigned u64 where
  width    := 64
  size     := UInt64.size
  toBitVec := UInt64.toBitVec
  toNat    := UInt64.toNat
  toNat_toBitVec := UInt64.toNat_toBitVec

@[simp, reducible]
instance : UnSigned usize where
  width    := System.Platform.numBits
  size     := USize.size
  toBitVec := USize.toBitVec
  toNat    := USize.toNat
  toNat_toBitVec := USize.toNat_toBitVec

/- Addition on unsigned rust integers. Panics on overflow -/
instance {α : Type} [UnSigned α]: HaxAdd α where
  add x y :=
    if (BitVec.uaddOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) then
      .fail .integerOverflow
    else pure (x + y)

/- Subtraction on unsigned rust integers. Panics on overflow -/
instance {α : Type} [UnSigned α] : HaxSub α where
  sub x y :=
    if (BitVec.usubOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) then
      .fail .integerOverflow
    else pure (x - y)

/- Multiplication on unsigned rust integers. Panics on overflow -/
instance {α : Type} [UnSigned α] : HaxMul α where
  mul x y :=
    if (BitVec.umulOverflow (UnSigned.toBitVec x) (UnSigned.toBitVec y)) then
      .fail .integerOverflow
    else pure (x * y)

/- Division on unsigned rust integers. Panics when dividing by zero  -/
instance {α : Type} [UnSigned α] : HaxDiv α where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x / y)

/- Division on unsigned rust integers. Panics when the modulus is zero  -/
instance {α : Type} [UnSigned α] : HaxRem α where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x % y)

/- Right shift on unsigned rust integers. Panics when shifting by more than the size -/
instance {α : Type} [UnSigned α]: HaxShiftRight α α where
  shiftRight x y :=
    if (UnSigned.width α) ≤ (UnSigned.toNat y) then .fail .integerOverflow
    else pure (x >>> y)

/- Signed operations -/
class Signed (α: Type)
  extends (LE α),
          (OfNat α 0),
          (Add α),
          (Sub α),
          (Mul α),
          (Div α),
          (Mod α),
          (ShiftRight α) where
  [dec: DecidableEq α]
  width    : Nat
  toBitVec : α → BitVec width
  toInt    : α → Int
  toInt_toBitVec : (x: α) -> (toBitVec x).toInt = (toInt x)
instance {α:Type} [i: Signed α] : DecidableEq α := i.dec


@[simp, reducible]
instance : Signed i8 where
  width    := 8
  toBitVec := Int8.toBitVec
  toInt    := Int8.toInt
  toInt_toBitVec := Int8.toInt_toBitVec

@[simp, reducible]
instance : Signed i16 where
  width    := 16
  toBitVec := Int16.toBitVec
  toInt    := Int16.toInt
  toInt_toBitVec := Int16.toInt_toBitVec

@[simp, reducible]
instance : Signed i32 where
  width    := 32
  toBitVec := Int32.toBitVec
  toInt    := Int32.toInt
  toInt_toBitVec := Int32.toInt_toBitVec

@[simp, reducible]
instance : Signed i64 where
  width    := 64
  toBitVec := Int64.toBitVec
  toInt    := Int64.toInt
  toInt_toBitVec := Int64.toInt_toBitVec

@[simp, reducible]
instance : Signed isize where
  width    := System.Platform.numBits
  toBitVec := ISize.toBitVec
  toInt    := ISize.toInt
  toInt_toBitVec := ISize.toInt_toBitVec


/- Addition on signed rust integers. Panics on overflow -/
instance {α : Type} [Signed α] : HaxAdd α where
  add x y :=
    if (BitVec.saddOverflow (Signed.toBitVec x) (Signed.toBitVec y)) then
      .fail .integerOverflow
    else pure (x + y)

/- Subtraction on signed rust integers. Panics on overflow -/
instance {α : Type} [Signed α] : HaxSub α where
  sub x y :=
    if (BitVec.ssubOverflow (Signed.toBitVec x) (Signed.toBitVec y)) then
      .fail .integerOverflow
    else pure (x - y)

/- Multiplication on signed rust integers. Panics on overflow -/
instance {α : Type} [Signed α] : HaxMul α where
  mul x y :=
    if (BitVec.smulOverflow (Signed.toBitVec x) (Signed.toBitVec y)) then
      .fail .integerOverflow
    else pure (x * y)

/- Division of signed rust integers. Panics on overflow (when x is IntMin and `y
   = -1`) and when dividing by zero -/
instance {α : Type} [Signed α] : HaxDiv α where
  div x y :=
    if BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y) then .fail .integerOverflow
    else if y = 0 then .fail .divisionByZero
    else pure (x / y)

/- Remainder of signed rust integers. Panics on overflow (when x is IntMin and `y
   = -1`) and when the modulus is zero -/
instance {α : Type} [Signed α] : HaxRem α where
  rem x y :=
    if BitVec.sdivOverflow (Signed.toBitVec x) (Signed.toBitVec y) then .fail .integerOverflow
    else if y = 0 then .fail .divisionByZero
    else pure (x % y)

/- Right shifting on signed integers. Panics when shifting by a negative number,
   or when shifting by more than the size. -/
instance {α : Type} [Signed α] : HaxShiftRight α α where
  shiftRight x y :=
    if 0 ≤ (Signed.toInt y) && (Signed.toInt y) < Int.ofNat (Signed.width α) then
      pure (x >>> y)
    else
      .fail .integerOverflow

/- Check that all operations are implemented -/

class Operations α where
  [instHaxAdd: HaxAdd α]
  [instHaxSub: HaxSub α]
  [instHaxMul: HaxMul α]
  [instHaxDiv: HaxDiv α]
  [instHaxRem: HaxRem α]
  [instHaxShiftRight: HaxShiftRight α α]

instance : Operations u8 where
instance : Operations u16 where
instance : Operations u32 where
instance : Operations u64 where
instance : Operations usize where
instance : Operations i8 where
instance : Operations i16 where
instance : Operations i32 where
instance : Operations i64 where
instance : Operations isize where



-- Custom instances
@[simp, spec]
instance : HaxShiftRight u64 i32 where
  shiftRight x y :=
    if 0 ≤ y && y ≤ 31 then pure (x >>> y.toNatClampNeg.toUInt64)
    else .fail .integerOverflow
