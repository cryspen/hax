import Hax.MissingLean.Init.Data.UInt.Lemmas

open Std
open Nat

def USize64 := UInt64

def USize64.size : Nat := UInt64.size
def USize64.ofNat (n : Nat) : USize64 := UInt64.ofNat n
def USize64.toNat (n : USize64) : Nat := UInt64.toNat n
def USize64.ofBitVec (n : BitVec 64) : USize64 := UInt64.ofBitVec n
def USize64.toBitVec (n : USize64) : BitVec 64 := UInt64.toBitVec n
def USize64.toFin (n : USize64) : Fin USize64.size := UInt64.toFin n

def USize64.ofNatLT (n : @& Nat) (h : LT.lt n USize64.size) : USize64 := UInt64.ofNatLT n h

def USize64.decEq (a b : USize64) : Decidable (Eq a b) := UInt64.decEq a b

instance : DecidableEq USize64 := USize64.decEq

instance : Inhabited USize64 where
  default := USize64.ofNatLT 0 (of_decide_eq_true rfl)

instance {n} : OfNat USize64 n := by unfold USize64; infer_instance

@[inline] def USize64.ofFin (a : Fin USize64.size) : USize64 := ⟨⟨a⟩⟩

def USize64.ofInt (x : Int) : USize64 := ofNat (x % 2 ^ 64).toNat

@[simp] theorem USize64.le_size : 2 ^ 32 ≤ USize64.size := by simp [USize64.size, UInt64.size]
@[simp] theorem USize64.size_le : USize64.size ≤ 2 ^ 64 := by simp [USize64.size, UInt64.size]

protected def USize64.add (a b : USize64) : USize64 := ⟨a.toBitVec + b.toBitVec⟩
protected def USize64.sub (a b : USize64) : USize64 := ⟨a.toBitVec - b.toBitVec⟩
protected def USize64.mul (a b : USize64) : USize64 := ⟨a.toBitVec * b.toBitVec⟩
protected def USize64.div (a b : USize64) : USize64 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
protected def USize64.pow (x : USize64) (n : Nat) : USize64 :=
  match n with
  | 0 => 1
  | n + 1 => USize64.mul (USize64.pow x n) x
protected def USize64.mod (a b : USize64) : USize64 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩

protected def USize64.land (a b : USize64) : USize64 := ⟨a.toBitVec &&& b.toBitVec⟩
protected def USize64.lor (a b : USize64) : USize64 := ⟨a.toBitVec ||| b.toBitVec⟩
protected def USize64.xor (a b : USize64) : USize64 := ⟨a.toBitVec ^^^ b.toBitVec⟩
protected def USize64.shiftLeft (a b : USize64) : USize64 := ⟨a.toBitVec <<< (USize64.mod b 64).toBitVec⟩
protected def USize64.shiftRight (a b : USize64) : USize64 := ⟨a.toBitVec >>> (USize64.mod b 64).toBitVec⟩
protected def USize64.lt (a b : USize64) : Prop := a.toBitVec < b.toBitVec
protected def USize64.le (a b : USize64) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add USize64       := ⟨USize64.add⟩
instance : Sub USize64       := ⟨USize64.sub⟩
instance : Mul USize64       := ⟨USize64.mul⟩
instance : Pow USize64 Nat   := ⟨USize64.pow⟩
instance : Mod USize64       := ⟨USize64.mod⟩

instance : HMod USize64 Nat USize64 := by unfold USize64; infer_instance

instance : Div USize64       := ⟨USize64.div⟩
instance : LT USize64        := ⟨USize64.lt⟩
instance : LE USize64        := ⟨USize64.le⟩

protected def USize64.complement (a : USize64) : USize64 := ⟨~~~a.toBitVec⟩
protected def USize64.neg (a : USize64) : USize64 := ⟨-a.toBitVec⟩

instance : Complement USize64 := ⟨USize64.complement⟩
instance : Neg USize64 := ⟨USize64.neg⟩
instance : AndOp USize64     := ⟨USize64.land⟩
instance : OrOp USize64      := ⟨USize64.lor⟩
instance : XorOp USize64       := ⟨USize64.xor⟩
instance : ShiftLeft USize64  := ⟨USize64.shiftLeft⟩
instance : ShiftRight USize64 := ⟨USize64.shiftRight⟩

def USize64.ofNat32 (n : @& Nat) (h : n < 4294967296) : USize64 :=
  USize64.ofNatLT n (Nat.lt_of_lt_of_le h USize64.le_size)
def UInt8.toUSize64 (a : UInt8) : USize64 :=
  USize64.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
def USize64.toUInt8 (a : USize) : UInt8 := a.toNat.toUInt8
def UInt16.toUSize64 (a : UInt16) : USize64 :=
  USize64.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
def USize64.toUInt16 (a : USize64) : UInt16 := a.toNat.toUInt16
def UInt32.toUSize64 (a : UInt32) : USize64 := USize64.ofNat32 a.toBitVec.toNat a.toBitVec.isLt
def USize64.toUInt32 (a : USize64) : UInt32 := a.toNat.toUInt32
def UInt64.toUSize64 (a : UInt64) : USize64 := a.toNat.toUInt64
def USize64.toUInt64 (a : USize64) : UInt64 := a
def Bool.toUSize64 (b : Bool) : USize64 := if b then 1 else 0
def USize64.decLt (a b : USize64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

def USize64.decLe (a b : USize64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

attribute [instance] USize64.decLt USize64.decLe

instance : Max USize64 := maxOfLe
instance : Min USize64 := minOfLe

instance {α} : GetElem (Array α) USize64 α fun xs i => i.toNat < xs.size where
  getElem xs i h := xs[i.toNat]

@[grind]
theorem USize64.umulOverflow_iff (x y : USize64) :
    BitVec.umulOverflow x.toBitVec y.toBitVec ↔ x.toNat * y.toNat ≥ 2 ^ 64 :=
  UInt64.umulOverflow_iff _ _

@[grind]
theorem USize64.uaddOverflow_iff (x y : USize64) :
    BitVec.uaddOverflow x.toBitVec y.toBitVec ↔ x.toNat + y.toNat ≥ 2 ^ 64 :=
  UInt64.uaddOverflow_iff _ _

@[grind =]
theorem USize64.toNat_mul_of_lt {a b : USize64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat :=
  UInt64.toNat_mul_of_lt h

@[grind =]
theorem USize64.toNat_add_of_lt {a b : USize64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat :=
  UInt64.toNat_add_of_lt h

@[grind ←]
theorem USize64.le_self_add {a b : USize64} (h : a.toNat + b.toNat < 2 ^ 64) :
    a ≤ a + b :=
  UInt64.le_self_add h

theorem USize64.succ_le_of_lt {a b : USize64} (h : a < b) :
    a + 1 ≤ b :=
  UInt64.succ_le_of_lt h

theorem USize64.add_le_of_le {a b c : USize64} (habc : a + b ≤ c) (hab : a.toNat + b.toNat < 2 ^ 64):
    a ≤ c :=
  UInt64.add_le_of_le habc hab

@[grind, simp]
protected theorem USize64.not_le {a b : USize64} : ¬ a ≤ b ↔ b < a :=
  UInt64.not_le

@[simp, grind]
theorem USize64.toNat_toBitVec (x : USize64) : x.toBitVec.toNat = x.toNat := (rfl)

@[simp, int_toBitVec, grind]
theorem USize64.toBitVec_ofNat (n : Nat) :
  USize64.toBitVec (no_index (OfNat.ofNat n)) = BitVec.ofNat _ n := (rfl)

@[simp, grind]
protected theorem USize64.toNat_add (a b : USize64) :
  (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add ..

@[grind]
theorem USize64.le_iff_toNat_le {a b : USize64} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

@[grind =]
theorem USize64.lt_iff_toNat_lt {a b : USize64} : a < b ↔ a.toNat < b.toNat := .rfl

@[grind]
theorem USize64.lt_ofNat_iff {n : USize64} {m : Nat} (h : m < size) :
  n < ofNat m ↔ n.toNat < m := UInt64.lt_ofNat_iff h

@[grind]
theorem USize64.ofNat_lt_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat :=
  UInt64.ofNat_lt_iff h

@[grind]
theorem USize64.le_ofNat_iff {n : USize64} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m :=
  UInt64.le_ofNat_iff h

@[grind]
theorem USize64.ofNat_le_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat :=
  UInt64.ofNat_le_iff h

attribute [grind] UInt64.toNat_ofNat_of_lt
attribute [grind] UInt64.toNat_ofNat_of_lt'

@[grind]
theorem USize64.toNat_ofNat_of_lt' {n : Nat} (h : n < size) : (ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

@[grind]
theorem USize64.toNat_ofNat_of_lt {n : Nat} (h : n < size) : toNat (OfNat.ofNat n) = n :=
  UInt64.toNat_ofNat_of_lt h


namespace Lean.Grind


instance : ToInt USize64 (.uint 64) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := sorry -- USize64.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := sorry -- by simpa using Int.lt_toNat.mp (USize64.toNat_lt x)

@[simp] theorem toInt_usize64 (x : USize64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero USize64 (.uint 64) where
  toInt_zero := sorry -- by simp

instance : ToInt.OfNat USize64 (.uint 64) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add USize64 (.uint 64) where
  toInt_add x y := by simp

instance : ToInt.Mul USize64 (.uint 64) where
  toInt_mul x y := sorry -- by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod USize64 (.uint 64) where
  toInt_mod x y := sorry -- by simp

instance : ToInt.Div USize64 (.uint 64) where
  toInt_div x y := sorry -- by simp

instance : ToInt.LE USize64 (.uint 64) where
  le_iff x y := sorry -- by simpa using USize64.le_iff_toBitVec_le

instance : ToInt.LT USize64 (.uint 64) where
  lt_iff x y := sorry -- by simpa using USize64.lt_iff_toBitVec_lt

end Lean.Grind
