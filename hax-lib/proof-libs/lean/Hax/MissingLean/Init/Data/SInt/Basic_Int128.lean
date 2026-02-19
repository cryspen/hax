import Hax.MissingLean.Init.Prelude
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.SInt

set_option autoImplicit true

-- Adapted from Init/Data/SInt/Basic.lean in the Lean 4 source code (Int64 section), with 64 replaced by 128.

structure Int128 where
  ofUInt128 :: toUInt128 : UInt128

abbrev Int128.size : Nat := 340282366920938463463374607431768211456

@[inline] def Int128.toBitVec (x : Int128) : BitVec 128 := x.toUInt128.toBitVec

theorem Int128.toBitVec.inj : {x y : Int128} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[inline] def UInt128.toInt128 (i : UInt128) : Int128 := Int128.ofUInt128 i

def Int128.ofInt (i : @& Int) : Int128 := ⟨⟨BitVec.ofInt 128 i⟩⟩

def Int128.ofNat (n : @& Nat) : Int128 := ⟨⟨BitVec.ofNat 128 n⟩⟩

abbrev Int.toInt128 := Int128.ofInt

abbrev Nat.toInt128 := Int128.ofNat

def Int128.toInt (i : Int128) : Int := i.toBitVec.toInt

@[suggest_for Int128.toNat, inline] def Int128.toNatClampNeg (i : Int128) : Nat := i.toInt.toNat

@[inline] def Int128.ofBitVec (b : BitVec 128) : Int128 := ⟨⟨b⟩⟩

def Int128.toInt8 (a : Int128) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

def Int128.toInt16 (a : Int128) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

def Int128.toInt32 (a : Int128) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def Int128.toInt64 (a : Int128) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def Int8.toInt128 (a : Int8) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int16.toInt128 (a : Int16) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int32.toInt128 (a : Int32) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int64.toInt128 (a : Int64) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int128.neg (i : Int128) : Int128 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int128 where
  toString i := toString i.toInt
instance : Repr Int128 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int128 := ⟨⟩

instance : Hashable Int128 where
  hash i := UInt64.ofInt i.toInt

instance Int128.instOfNat : OfNat Int128 n := ⟨Int128.ofNat n⟩
instance Int128.instNeg : Neg Int128 where
  neg := Int128.neg

abbrev Int128.maxValue : Int128 := 170141183460469231731687303715884105727
abbrev Int128.minValue : Int128 := -170141183460469231731687303715884105728

@[inline]
def Int128.ofIntLE (i : Int) (_hl : Int128.minValue.toInt ≤ i) (_hr : i ≤ Int128.maxValue.toInt) : Int128 :=
  Int128.ofInt i

def Int128.ofIntTruncate (i : Int) : Int128 :=
  if hl : Int128.minValue.toInt ≤ i then
    if hr : i ≤ Int128.maxValue.toInt then
      Int128.ofIntLE i hl hr
    else
      Int128.minValue
  else
    Int128.minValue

protected def Int128.add (a b : Int128) : Int128 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩

protected def Int128.sub (a b : Int128) : Int128 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩

protected def Int128.mul (a b : Int128) : Int128 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩

protected def Int128.div (a b : Int128) : Int128 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩

protected def Int128.pow (x : Int128) (n : Nat) : Int128 :=
  match n with
  | 0 => 1
  | n + 1 => Int128.mul (Int128.pow x n) x

protected def Int128.mod (a b : Int128) : Int128 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩

protected def Int128.land (a b : Int128) : Int128 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩

protected def Int128.lor (a b : Int128) : Int128 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩

protected def Int128.xor (a b : Int128) : Int128 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩

protected def Int128.shiftLeft (a b : Int128) : Int128 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 128)⟩⟩

protected def Int128.shiftRight (a b : Int128) : Int128 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 128)⟩⟩

protected def Int128.complement (a : Int128) : Int128 := ⟨⟨~~~a.toBitVec⟩⟩

protected def Int128.abs (a : Int128) : Int128 := ⟨⟨a.toBitVec.abs⟩⟩

def Int128.decEq (a b : Int128) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int128.noConfusion h' (fun h' => absurd h' h))

protected def Int128.lt (a b : Int128) : Prop := a.toBitVec.slt b.toBitVec

protected def Int128.le (a b : Int128) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int128 where
  default := 0

instance : Add Int128         := ⟨Int128.add⟩
instance : Sub Int128         := ⟨Int128.sub⟩
instance : Mul Int128         := ⟨Int128.mul⟩
instance : Pow Int128 Nat     := ⟨Int128.pow⟩
instance : Mod Int128         := ⟨Int128.mod⟩
instance : Div Int128         := ⟨Int128.div⟩
instance : LT Int128          := ⟨Int128.lt⟩
instance : LE Int128          := ⟨Int128.le⟩
instance : Complement Int128  := ⟨Int128.complement⟩
instance : AndOp Int128       := ⟨Int128.land⟩
instance : OrOp Int128        := ⟨Int128.lor⟩
instance : XorOp Int128         := ⟨Int128.xor⟩
instance : ShiftLeft Int128   := ⟨Int128.shiftLeft⟩
instance : ShiftRight Int128  := ⟨Int128.shiftRight⟩
instance : DecidableEq Int128 := Int128.decEq

def Bool.toInt128 (b : Bool) : Int128 := if b then 1 else 0

def Int128.decLt (a b : Int128) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

def Int128.decLe (a b : Int128) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance_reducible, instance] Int128.decLt Int128.decLe

instance : Max Int128 := maxOfLe
instance : Min Int128 := minOfLe
