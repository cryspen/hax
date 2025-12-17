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
