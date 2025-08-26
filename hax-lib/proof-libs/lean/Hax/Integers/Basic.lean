import Hax.Result

/-
  Integer types are represented as the corresponding type in Lean
-/
abbrev u8 := UInt8
abbrev u16 := UInt16
abbrev u32 := UInt32
abbrev u64 := UInt64
abbrev usize := USize
abbrev i8 := Int8
abbrev i16 := Int16
abbrev i32 := Int32
abbrev i64 := Int64
abbrev isize := ISize

/-- Class of objects that can be transformed into Nat -/
class ToNat (α: Type) where
  toNat : α -> Nat

@[simp]
instance : ToNat USize where
  toNat x := x.toNat
@[simp]
instance : ToNat u64 where
  toNat x := x.toNat
@[simp]
instance : ToNat u32 where
  toNat x := x.toNat
@[simp]
instance : ToNat u16 where
  toNat x := x.toNat
@[simp]
instance : ToNat Nat where
  toNat x := x

/-
  Coercions between integer types
-/
-- TODO : make sure all are necessary, document their use-cases
@[simp, spec]
instance : Coe i32 (Result i64) where
  coe x := pure (x.toInt64)

@[simp]
instance : Coe USize Nat where
  coe x := x.toNat

@[simp]
instance : Coe u32 Nat where
  coe x := x.toNat

@[simp]
instance : Coe Nat usize where
  coe x := USize.ofNat x

@[simp]
instance : Coe Nat i32 where
  coe x := Int32.ofNat x

@[simp]
instance : Coe USize UInt32 where
  coe x := x.toUInt32

@[simp]
instance : Coe USize (Result u32) where
  coe x := if x.toNat < UInt32.size then pure (x.toUInt32)
           else Result.fail .integerOverflow

@[simp]
instance {α β} : Coe (α -> usize -> β) (α -> Nat -> β) where
  coe f a x := f a (USize.ofNat x)

@[simp]
instance {α β} : Coe (α -> i32 -> β) (α -> Nat -> β) where
  coe f a x := f a (Int32.ofNat x)

@[simp]
instance {n} : OfNat (Result Nat) n where
  ofNat := pure (n)
