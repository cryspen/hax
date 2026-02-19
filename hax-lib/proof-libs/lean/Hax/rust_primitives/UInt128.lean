import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt

-- Adapted from Init/Prelude.lean

abbrev UInt128.size : Nat := 340282366920938463463374607431768211456

structure UInt128 where
  ofBitVec ::
  toBitVec : BitVec 128

def UInt128.ofNatLT (n : @& Nat) (h : LT.lt n UInt128.size) : UInt128 where
  toBitVec := BitVec.ofNatLT n h

def UInt128.decEq (a b : UInt128) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt128.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt128 := UInt128.decEq

instance : Inhabited UInt128 where
  default := UInt128.ofNatLT 0 (of_decide_eq_true rfl)

-- Adapted from Init/Data/UInt/BasicAux.lean

def UInt128.toFin (x : UInt128) : Fin UInt128.size := x.toBitVec.toFin

def UInt128.ofNat (n : @& Nat) : UInt128 := ⟨BitVec.ofNat 128 n⟩

def UInt128.ofNatTruncate (n : Nat) : UInt128 :=
  if h : n < UInt128.size then
    UInt128.ofNatLT n h
  else
    UInt128.ofNatLT (UInt128.size - 1) (by decide)

abbrev Nat.toUInt128 := UInt128.ofNat

def UInt128.toNat (n : UInt128) : Nat := n.toBitVec.toNat

def UInt128.toUInt8 (a : UInt128) : UInt8 := a.toNat.toUInt8
def UInt128.toUInt16 (a : UInt128) : UInt16 := a.toNat.toUInt16
def UInt128.toUInt32 (a : UInt128) : UInt32 := a.toNat.toUInt32
def UInt128.toUInt64 (a : UInt128) : UInt64 := a.toNat.toUInt64
def UInt128.toUSize (a : UInt128) : USize := a.toNat.toUSize

def UInt8.toUInt128 (a : UInt8) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt16.toUInt128 (a : UInt16) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt32.toUInt128 (a : UInt32) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt64.toUInt128 (a : UInt64) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def USize.toUInt128 (a : USize) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩

instance UInt128.instOfNat (n : Nat) : OfNat UInt128 n := ⟨UInt128.ofNat n⟩

-- Adapted from Init/Data/UInt/Basic.lean

@[inline] def UInt128.ofFin (a : Fin UInt128.size) : UInt128 := ⟨⟨a⟩⟩

def UInt128.ofInt (x : Int) : UInt128 := UInt128.ofNat (x % 2 ^ 128).toNat

protected def UInt128.add (a b : UInt128) : UInt128 := ⟨a.toBitVec + b.toBitVec⟩
protected def UInt128.sub (a b : UInt128) : UInt128 := ⟨a.toBitVec - b.toBitVec⟩
protected def UInt128.mul (a b : UInt128) : UInt128 := ⟨a.toBitVec * b.toBitVec⟩
protected def UInt128.div (a b : UInt128) : UInt128 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
protected def UInt128.pow (x : UInt128) (n : Nat) : UInt128 :=
  match n with
  | 0 => 1
  | n + 1 => UInt128.mul (UInt128.pow x n) x
protected def UInt128.mod (a b : UInt128) : UInt128 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩

set_option linter.missingDocs false in
@[deprecated UInt128.mod (since := "2024-09-23")]
protected def UInt128.modn (a : UInt128) (n : Nat) : UInt128 := ⟨Fin.modn a.toFin n⟩

protected def UInt128.land (a b : UInt128) : UInt128 := ⟨a.toBitVec &&& b.toBitVec⟩
protected def UInt128.lor (a b : UInt128) : UInt128 := ⟨a.toBitVec ||| b.toBitVec⟩
protected def UInt128.xor (a b : UInt128) : UInt128 := ⟨a.toBitVec ^^^ b.toBitVec⟩
protected def UInt128.shiftLeft (a b : UInt128) : UInt128 := ⟨a.toBitVec <<< (UInt128.mod b 128).toBitVec⟩
protected def UInt128.shiftRight (a b : UInt128) : UInt128 := ⟨a.toBitVec >>> (UInt128.mod b 128).toBitVec⟩
protected def UInt128.lt (a b : UInt128) : Prop := a.toBitVec < b.toBitVec
protected def UInt128.le (a b : UInt128) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt128       := ⟨UInt128.add⟩
instance : Sub UInt128       := ⟨UInt128.sub⟩
instance : Mul UInt128       := ⟨UInt128.mul⟩
instance : Pow UInt128 Nat   := ⟨UInt128.pow⟩
instance : Mod UInt128       := ⟨UInt128.mod⟩

set_option linter.deprecated false in
instance : HMod UInt128 Nat UInt128 := ⟨UInt128.modn⟩

instance : Div UInt128       := ⟨UInt128.div⟩
instance : LT UInt128        := ⟨UInt128.lt⟩
instance : LE UInt128        := ⟨UInt128.le⟩

protected def UInt128.complement (a : UInt128) : UInt128 := ⟨~~~a.toBitVec⟩
protected def UInt128.neg (a : UInt128) : UInt128 := ⟨-a.toBitVec⟩

instance : Complement UInt128 := ⟨UInt128.complement⟩
instance : Neg UInt128 := ⟨UInt128.neg⟩
instance : AndOp UInt128     := ⟨UInt128.land⟩
instance : OrOp UInt128      := ⟨UInt128.lor⟩
instance : XorOp UInt128       := ⟨UInt128.xor⟩
instance : ShiftLeft UInt128  := ⟨UInt128.shiftLeft⟩
instance : ShiftRight UInt128 := ⟨UInt128.shiftRight⟩

def Bool.toUInt128 (b : Bool) : UInt128 := if b then 1 else 0

def UInt128.decLt (a b : UInt128) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

def UInt128.decLe (a b : UInt128) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

attribute [instance_reducible, instance] UInt128.decLt UInt128.decLe

instance : Max UInt128 := maxOfLe
instance : Min UInt128 := minOfLe

-- Adapted from Lean/ToExpr.lean

open Lean in
instance : ToExpr UInt128 where
  toTypeExpr := mkConst ``UInt128
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``UInt128) r
      (.app (.const ``UInt128.instOfNat []) r)

-- Adapted from Lean/Meta/Tactic/Simp/BuiltinSimpProcs/SInt.lean

namespace UInt128

open Lean Meta Simp

def fromExpr (e : Expr) : SimpM (Option UInt128) := do
  let some (n, _) ← getOfNatValue? e ``UInt128 | return none
  return ofNat n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → UInt128) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceAdd ((_ + _ : UInt128)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : UInt128)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : UInt128)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : UInt128)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : UInt128)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] reduceLT  (( _ : UInt128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : UInt128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : UInt128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : UInt128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : UInt128) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : UInt128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : UInt128) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : UInt128) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfNatLT (ofNatLT _ _) := fun e => do
  unless e.isAppOfArity ``ofNatLT 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToNat (toNat _) := fun e => do
  unless e.isAppOfArity ``toNat 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : UInt128)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end UInt128

-- Adapted from Init/Data/UInt/Lemmas.lean

set_option autoImplicit true
open Std

declare_uint_theorems UInt128 128
@[simp] theorem UInt128.toNat_toUInt64 (x : UInt128) : x.toUInt64.toNat = x.toNat % 2 ^ 64 := (rfl)

theorem UInt128.ofNat_mod_size : ofNat (x % 2 ^ 128) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat]

theorem UInt128.ofNat_size : ofNat size = 0 := by decide

theorem UInt128.lt_ofNat_iff {n : UInt128} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt128.ofNat_lt_iff {n : UInt128} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt128.le_ofNat_iff {n : UInt128} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem UInt128.ofNat_le_iff {n : UInt128} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

protected theorem UInt128.mod_eq_of_lt {a b : UInt128} (h : a < b) : a % b = a := UInt128.toNat_inj.1 (Nat.mod_eq_of_lt h)

@[simp] theorem UInt128.toNat_lt (n : UInt128) : n.toNat < 2 ^ 128 := n.toFin.isLt

theorem USize.size_le_uint128Size : USize.size ≤ UInt128.size := by
  cases USize.size_eq <;> simp_all +decide

theorem USize.size_dvd_uInt128Size : USize.size ∣ UInt128.size := by cases USize.size_eq <;> simp_all +decide

@[simp] theorem mod_uInt128Size_uSizeSize (n : Nat) : n % UInt128.size % USize.size = n % USize.size :=
  Nat.mod_mod_of_dvd _ USize.size_dvd_uInt128Size

@[simp] theorem UInt128.size_sub_one_mod_uSizeSize : 340282366920938463463374607431768211455 % USize.size = USize.size - 1 := by
  cases USize.size_eq <;> simp_all +decide

@[simp] theorem UInt8.toNat_mod_uInt128Size (n : UInt8) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt16.toNat_mod_uInt128Size (n : UInt16) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt32.toNat_mod_uInt128Size (n : UInt32) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt64.toNat_mod_uInt128Size (n : UInt64) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt128.toNat_mod_size (n : UInt128) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt
@[simp] theorem USize.toNat_mod_uInt128Size (n : USize) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

-- @[simp] theorem UInt8.toUInt128_mod_256 (n : UInt8) : n.toUInt128 % 256 = n.toUInt128 := UInt128.toNat.inj (by simp)
-- @[simp] theorem UInt16.toUInt128_mod_65536 (n : UInt16) : n.toUInt128 % 65536 = n.toUInt128 := UInt128.toNat.inj (by simp)
-- @[simp] theorem UInt32.toUInt128_mod_4294967296 (n : UInt32) : n.toUInt128 % 4294967296 = n.toUInt128 := UInt128.toNat.inj (by simp)

@[simp] theorem Fin.mk_uInt128ToNat (n : UInt128) : Fin.mk n.toNat (by exact n.toFin.isLt) = n.toFin := (rfl)

@[simp] theorem BitVec.ofNatLT_uInt128ToNat (n : UInt128) : BitVec.ofNatLT n.toNat (by exact n.toFin.isLt) = n.toBitVec := (rfl)

@[simp] theorem BitVec.ofFin_uInt128ToFin (n : UInt128) : BitVec.ofFin n.toFin = n.toBitVec := (rfl)

-- @[simp] theorem UInt8.toFin_toUInt128 (n : UInt8) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)
-- @[simp] theorem UInt16.toFin_toUInt128 (n : UInt16) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)
-- @[simp] theorem UInt32.toFin_toUInt128 (n : UInt32) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)
-- @[simp] theorem USize.toFin_toUInt128 (n : USize) : n.toUInt128.toFin = n.toFin.castLE size_le_uint128Size := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt8 (n : UInt128) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := (rfl)
@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt16 (n : UInt128) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := (rfl)
@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt32 (n : UInt128) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

-- @[simp, int_toBitVec] theorem UInt8.toBitVec_toUInt128 (n : UInt8) : n.toUInt128.toBitVec = n.toBitVec.setWidth 128 := (rfl)
-- @[simp, int_toBitVec] theorem UInt16.toBitVec_toUInt128 (n : UInt16) : n.toUInt128.toBitVec = n.toBitVec.setWidth 128 := (rfl)
-- @[simp, int_toBitVec] theorem UInt32.toBitVec_toUInt128 (n : UInt32) : n.toUInt128.toBitVec = n.toBitVec.setWidth 128 := (rfl)
-- @[simp, int_toBitVec] theorem USize.toBitVec_toUInt128 (n : USize) : n.toUInt128.toBitVec = n.toBitVec.setWidth 128 :=
--   BitVec.eq_of_toNat_eq (by simp)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUSize (n : UInt128) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)

-- @[simp] theorem UInt128.ofNatLT_uInt8ToNat (n : UInt8) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofNatLT_uInt16ToNat (n : UInt16) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofNatLT_uInt32ToNat (n : UInt32) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofNatLT_toNat (n : UInt128) : UInt128.ofNatLT n.toNat n.toNat_lt = n := (rfl)
-- @[simp] theorem UInt128.ofNatLT_uSizeToNat (n : USize) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)

theorem UInt8.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt16.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt32.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt32.ofNatLT n.toNat h = n.toUInt32 :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem USize.ofNatLT_uInt128ToNat (n : UInt128) (h) : USize.ofNatLT n.toNat h = n.toUSize :=
  USize.toNat.inj (by simp [Nat.mod_eq_of_lt h])

@[simp] theorem UInt128.ofFin_toFin (n : UInt128) : UInt128.ofFin n.toFin = n := (rfl)

@[simp] theorem UInt128.toFin_ofFin (n : Fin UInt128.size) : (UInt128.ofFin n).toFin = n := (rfl)

-- @[simp] theorem UInt128.ofFin_uint8ToFin (n : UInt8) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofFin_uint16ToFin (n : UInt16) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofFin_uint32ToFin (n : UInt32) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem Nat.toUInt128_eq {n : Nat} : n.toUInt128 = UInt128.ofNat n := (rfl)

@[simp] theorem UInt8.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := (rfl)
@[simp] theorem UInt16.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := (rfl)
@[simp] theorem UInt32.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := (rfl)

-- @[simp] theorem UInt128.ofBitVec_uInt8ToBitVec (n : UInt8) :
--     UInt128.ofBitVec (n.toBitVec.setWidth 128) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofBitVec_uInt16ToBitVec (n : UInt16) :
--     UInt128.ofBitVec (n.toBitVec.setWidth 128) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofBitVec_uInt32ToBitVec (n : UInt32) :
--     UInt128.ofBitVec (n.toBitVec.setWidth 128) = n.toUInt128 := (rfl)
-- @[simp] theorem UInt128.ofBitVec_uSizeToBitVec (n : USize) :
--     UInt128.ofBitVec (n.toBitVec.setWidth 128) = n.toUInt128 :=
--   UInt128.toNat.inj (by simp)

@[simp] theorem USize.ofBitVec_uInt128ToBitVec (n : UInt128) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt8.ofNat_uInt128ToNat (n : UInt128) : UInt8.ofNat n.toNat = n.toUInt8 := (rfl)
@[simp] theorem UInt16.ofNat_uInt128ToNat (n : UInt128) : UInt16.ofNat n.toNat = n.toUInt16 := (rfl)
@[simp] theorem UInt32.ofNat_uInt128ToNat (n : UInt128) : UInt32.ofNat n.toNat = n.toUInt32 := (rfl)

-- @[simp] theorem UInt128.ofNat_uInt8ToNat (n : UInt8) : UInt128.ofNat n.toNat = n.toUInt128 :=
--   UInt128.toNat.inj (by simp)
-- @[simp] theorem UInt128.ofNat_uInt16ToNat (n : UInt16) : UInt128.ofNat n.toNat = n.toUInt128 :=
--   UInt128.toNat.inj (by simp)
-- @[simp] theorem UInt128.ofNat_uInt32ToNat (n : UInt32) : UInt128.ofNat n.toNat = n.toUInt128 :=
--   UInt128.toNat.inj (by simp)
-- @[simp] theorem UInt128.ofNat_uSizeToNat (n : USize) : UInt128.ofNat n.toNat = n.toUInt128 :=
--   UInt128.toNat.inj (by simp)

@[simp] theorem USize.ofNat_uInt128ToNat (n : UInt128) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)

theorem UInt128.ofNatLT_eq_ofNat (n : Nat) {h} : UInt128.ofNatLT n h = UInt128.ofNat n :=
  UInt128.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt128.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt128.size) :
    UInt128.ofNatTruncate n = UInt128.ofNat n := by
  simp [ofNatTruncate, hn, UInt128.ofNatLT_eq_ofNat]

-- @[simp] theorem UInt128.ofNatTruncate_uInt8ToNat (n : UInt8) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
--   rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
--   exact Nat.lt_trans (n.toNat_lt) (by decide)
-- @[simp] theorem UInt128.ofNatTruncate_uInt16ToNat (n : UInt16) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
--   rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
--   exact Nat.lt_trans (n.toNat_lt) (by decide)
-- @[simp] theorem UInt128.ofNatTruncate_uInt32ToNat (n : UInt32) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
--   rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt32ToNat]
--   exact Nat.lt_trans (n.toNat_lt) (by decide)
-- @[simp] theorem UInt128.ofNatTruncate_uInt64ToNat (n : UInt64) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
--   rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt64ToNat]
--   exact Nat.lt_trans n.toNat_lt (by norm_num [UInt64.size, UInt128.size])
@[simp] theorem UInt128.ofNatTruncate_toNat (n : UInt128) : UInt128.ofNatTruncate n.toNat = n := by
  rw [UInt128.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

-- @[simp] theorem UInt8.toUInt8_toUInt128 (n : UInt8) : n.toUInt128.toUInt8 = n :=
--   UInt8.toNat.inj (by simp)
-- @[simp] theorem UInt8.toUInt16_toUInt128 (n : UInt8) : n.toUInt128.toUInt16 = n.toUInt16 :=
--   UInt16.toNat.inj (by simp)
-- @[simp] theorem UInt8.toUInt32_toUInt128 (n : UInt8) : n.toUInt128.toUInt32 = n.toUInt32 :=
--   UInt32.toNat.inj (by simp)
-- @[simp] theorem UInt8.toUInt64_toUInt128 (n : UInt8) : n.toUInt128.toUInt64 = n.toUInt64 :=
--   UInt64.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt128_toUInt16 (n : UInt8) : n.toUInt16.toUInt128 = n.toUInt128 := (rfl)
@[simp] theorem UInt8.toUInt128_toUInt32 (n : UInt8) : n.toUInt32.toUInt128 = n.toUInt128 := (rfl)
@[simp] theorem UInt8.toUInt128_toUInt64 (n : UInt8) : n.toUInt64.toUInt128 = n.toUInt128 := (rfl)

-- @[simp] theorem UInt16.toUInt8_toUInt128 (n : UInt16) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)
-- @[simp] theorem UInt16.toUInt16_toUInt128 (n : UInt16) : n.toUInt128.toUInt16 = n :=
--   UInt16.toNat.inj (by simp)
-- @[simp] theorem UInt16.toUInt32_toUInt128 (n : UInt16) : n.toUInt128.toUInt32 = n.toUInt32 :=
--   UInt32.toNat.inj (by simp)
-- @[simp] theorem UInt16.toUInt64_toUInt128 (n : UInt16) : n.toUInt128.toUInt64 = n.toUInt64 :=
--   UInt64.toNat.inj (by simp)
-- @[simp] theorem UInt16.toUInt128_toUInt8 (n : UInt16) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)
@[simp] theorem UInt16.toUInt128_toUInt32 (n : UInt16) : n.toUInt32.toUInt128 = n.toUInt128 := (rfl)
@[simp] theorem UInt16.toUInt128_toUInt64 (n : UInt16) : n.toUInt64.toUInt128 = n.toUInt128 := (rfl)

-- @[simp] theorem UInt32.toUInt8_toUInt128 (n : UInt32) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)
-- @[simp] theorem UInt32.toUInt16_toUInt128 (n : UInt32) : n.toUInt128.toUInt16 = n.toUInt16 := (rfl)
-- @[simp] theorem UInt32.toUInt32_toUInt128 (n : UInt32) : n.toUInt128.toUInt32 = n :=
--   UInt32.toNat.inj (by simp)
-- @[simp] theorem UInt32.toUInt64_toUInt128 (n : UInt32) : n.toUInt128.toUInt64 = n.toUInt64 :=
--   UInt64.toNat.inj (by simp)
-- @[simp] theorem UInt32.toUInt128_toUInt8 (n : UInt32) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)
-- @[simp] theorem UInt32.toUInt128_toUInt16 (n : UInt32) : n.toUInt16.toUInt128 = n.toUInt128 % 65536 := (rfl)
@[simp] theorem UInt32.toUInt128_toUInt64 (n : UInt32) : n.toUInt64.toUInt128 = n.toUInt128 := (rfl)

-- @[simp] theorem UInt64.toUInt8_toUInt128 (n : UInt64) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)
-- @[simp] theorem UInt64.toUInt16_toUInt128 (n : UInt64) : n.toUInt128.toUInt16 = n.toUInt16 := (rfl)
-- @[simp] theorem UInt64.toUInt32_toUInt128 (n : UInt64) : n.toUInt128.toUInt32 = n.toUInt32 := (rfl)
-- @[simp] theorem UInt64.toUInt64_toUInt128 (n : UInt64) : n.toUInt128.toUInt64 = n :=
--   UInt64.toNat.inj (by simp)
-- @[simp] theorem UInt64.toUInt128_toUInt8 (n : UInt64) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)
-- @[simp] theorem UInt64.toUInt128_toUInt16 (n : UInt64) : n.toUInt16.toUInt128 = n.toUInt128 % 65536 := (rfl)
-- @[simp] theorem UInt64.toUInt128_toUInt32 (n : UInt64) : n.toUInt32.toUInt128 = n.toUInt128 % 4294967296 := (rfl)

@[simp] theorem UInt128.toUInt8_toUInt16 (n : UInt128) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt8_toUInt32 (n : UInt128) : n.toUInt32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt8_toUInt64 (n : UInt128) : n.toUInt64.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt16_toUInt8 (n : UInt128) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt16_toUInt32 (n : UInt128) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt16_toUInt64 (n : UInt128) : n.toUInt64.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt32_toUInt8 (n : UInt128) : n.toUInt8.toUInt32 = n.toUInt32 % 256 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt32_toUInt16 (n : UInt128) : n.toUInt16.toUInt32 = n.toUInt32 % 65536 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt32_toUInt64 (n : UInt128) : n.toUInt64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt64_toUInt8 (n : UInt128) : n.toUInt8.toUInt64 = n.toUInt64 % 256 :=
  UInt64.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt64_toUInt16 (n : UInt128) : n.toUInt16.toUInt64 = n.toUInt64 % 65536 :=
  UInt64.toNat.inj (by simp)
@[simp] theorem UInt128.toUInt64_toUInt32 (n : UInt128) : n.toUInt32.toUInt64 = n.toUInt64 % 4294967296 :=
  UInt64.toNat.inj (by simp)
-- @[simp] theorem UInt128.toUInt128_toUInt8 (n : UInt128) : n.toUInt8.toUInt128 = n % 256 := (rfl)
-- @[simp] theorem UInt128.toUInt128_toUInt16 (n : UInt128) : n.toUInt16.toUInt128 = n % 65536 := (rfl)
-- @[simp] theorem UInt128.toUInt128_toUInt32 (n : UInt128) : n.toUInt32.toUInt128 = n % 4294967296 := (rfl)
-- @[simp] theorem UInt128.toUInt128_toUInt64 (n : UInt128) : n.toUInt64.toUInt128 = n % 18446744073709551616 :=
--   UInt128.toNat.inj (by simp)

@[simp] theorem UInt128.toNat_ofFin (x : Fin UInt128.size) : (UInt128.ofFin x).toNat = x.val := (rfl)

theorem UInt128.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toNat = n := by rw [UInt128.ofNatTruncate, dif_pos hn, toNat_ofNatLT]

theorem UInt128.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toNat = UInt128.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]

theorem UInt128.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt128.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toFin = ⟨UInt128.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt128.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt128.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt128.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])

-- theorem UInt128.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
--     (UInt128.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]

theorem UInt128.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

-- theorem UInt128.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
--     (UInt128.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]

theorem UInt128.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

-- theorem UInt128.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
--     (UInt128.ofNatTruncate n).toUInt32 = UInt32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt32_ofNatLT]

theorem UInt128.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

-- theorem UInt128.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
--     (UInt128.ofNatTruncate n).toUSize = USize.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize_ofNatLT]

theorem UInt128.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUSize = USize.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt128.toUInt8_div (a b : UInt128) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUInt16_div (a b : UInt128) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUInt32_div (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUSize_div (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (Nat.div_mod_eq_mod_div_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem UInt128.toUSize_div_of_toNat_lt (a b : UInt128) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) :
    (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUInt8_mod (a b : UInt128) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt16_mod (a b : UInt128) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt32_mod (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUSize_mod (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem UInt128.toUSize_mod_of_toNat_lt (a b : UInt128) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt8_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUInt16_mod_of_dvd (a b : UInt128)(hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUInt32_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUSize_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.dvd_trans hb UInt32.size_dvd_usizeSize))

theorem UInt128.toUSize_mod_of_dvd_usizeSize (a b : UInt128) (hb : b.toNat ∣ USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

-- theorem UInt128.toUInt8_eq (a b : UInt128) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
--   simp [← UInt8.toNat_inj, ← UInt128.toNat_inj]

-- theorem UInt128.toUInt16_eq (a b : UInt128) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
--   simp [← UInt16.toNat_inj, ← UInt128.toNat_inj]

-- theorem UInt128.toUInt32_eq (a b : UInt128) : a.toUInt32 = b.toUInt32 ↔ a % 4294967296 = b % 4294967296 := by
--   simp [← UInt32.toNat_inj, ← UInt128.toNat_inj]

theorem UInt128.lt_iff_toFin_lt {a b : UInt128} : a < b ↔ a.toFin < b.toFin := Iff.rfl

theorem UInt128.le_iff_toFin_le {a b : UInt128} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl

protected theorem UInt128.sub_eq_add_neg (a b : UInt128) : a - b = a + (-b) := UInt128.toBitVec_inj.1 (BitVec.sub_eq_add_neg _ _)

protected theorem UInt128.add_neg_eq_sub {a b : UInt128} : a + -b = a - b := UInt128.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem UInt128.neg_one_eq : (-1 : UInt128) = 340282366920938463463374607431768211455 := (rfl)

theorem UInt128.toBitVec_zero : toBitVec 0 = 0#128 := (rfl)

theorem UInt128.toBitVec_one : toBitVec 1 = 1#128 := (rfl)

theorem UInt128.neg_eq_neg_one_mul (a : UInt128) : -a = -1 * a := by
  apply UInt128.toBitVec_inj.1
  rw [UInt128.toBitVec_neg, UInt128.toBitVec_mul, UInt128.toBitVec_neg, UInt128.toBitVec_one, BitVec.neg_eq_neg_one_mul]

theorem UInt128.sub_eq_add_mul (a b : UInt128) : a - b = a + 340282366920938463463374607431768211455 * b := by
  rw [UInt128.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]

theorem UInt128.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt128) : UInt128.ofNat a = b ↔ a % 2 ^ 128 = b.toNat := by
  simp [← UInt128.toNat_inj]

-- theorem UInt128.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt128.ofNat (a - b) = UInt128.ofNat a - UInt128.ofNat b := by
--   rw [(Nat.sub_add_cancel hab ▸ UInt128.ofNat_add (a - b) b :), UInt128.add_sub_cancel]

-- theorem UInt128.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 128) (hab : b ≤ a) :
--     UInt128.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt128.ofNatLT a ha - UInt128.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
--   simp [UInt128.ofNatLT_eq_ofNat, UInt128.ofNat_sub hab]

theorem UInt128.ofFin_lt_iff_lt {a b : Fin UInt128.size} : UInt128.ofFin a < UInt128.ofFin b ↔ a < b := Iff.rfl

theorem UInt128.ofFin_le_iff_le {a b : Fin UInt128.size} : UInt128.ofFin a ≤ UInt128.ofFin b ↔ a ≤ b := Iff.rfl

theorem UInt128.ofBitVec_lt_iff_lt {a b : BitVec 128} : UInt128.ofBitVec a < UInt128.ofBitVec b ↔ a < b := Iff.rfl

theorem UInt128.ofBitVec_le_iff_le {a b : BitVec 128} : UInt128.ofBitVec a ≤ UInt128.ofBitVec b ↔ a ≤ b := Iff.rfl

theorem UInt128.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNatLT a ha < UInt128.ofNatLT b hb ↔ a < b := Iff.rfl

theorem UInt128.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNatLT a ha ≤ UInt128.ofNatLT b hb ↔ a ≤ b := Iff.rfl

theorem UInt128.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNat a < UInt128.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]

theorem UInt128.ofNat_le_iff_le {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNat a ≤ UInt128.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]

theorem UInt128.toNat_one : (1 : UInt128).toNat = 1 := (rfl)

-- theorem UInt128.zero_lt_one : (0 : UInt128) < 1 := by simp

-- theorem UInt128.zero_ne_one : (0 : UInt128) ≠ 1 := by simp

protected theorem UInt128.add_assoc (a b c : UInt128) : a + b + c = a + (b + c) :=
  UInt128.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

protected theorem UInt128.add_comm (a b : UInt128) : a + b = b + a := UInt128.toBitVec_inj.1 (BitVec.add_comm _ _)

protected theorem UInt128.add_left_neg (a : UInt128) : -a + a = 0 := UInt128.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem UInt128.add_right_neg (a : UInt128) : a + -a = 0 := UInt128.toBitVec_inj.1 (BitVec.add_right_neg _)

protected theorem UInt128.eq_sub_iff_add_eq {a b c : UInt128} : a = c - b ↔ a + b = c := by
  simpa [← UInt128.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem UInt128.sub_eq_iff_eq_add {a b c : UInt128} : a - b = c ↔ a = c + b := by
  simpa [← UInt128.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

protected theorem UInt128.neg_add {a b : UInt128} : - (a + b) = -a - b := UInt128.toBitVec_inj.1 BitVec.neg_add

protected theorem UInt128.mul_comm (a b : UInt128) : a * b = b * a := UInt128.toBitVec_inj.1 (BitVec.mul_comm _ _)

protected theorem UInt128.mul_assoc (a b c : UInt128) : a * b * c = a * (b * c) := UInt128.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

protected theorem UInt128.pow_succ (x : UInt128) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem UInt128.mul_add {a b c : UInt128} : a * (b + c) = a * b + a * c :=
    UInt128.toBitVec_inj.1 BitVec.mul_add

protected theorem UInt128.add_mul {a b c : UInt128} : (a + b) * c = a * c + b * c := by
  rw [UInt128.mul_comm, UInt128.mul_add, UInt128.mul_comm a c, UInt128.mul_comm c b]

-- protected theorem UInt128.mul_succ {a b : UInt128} : a * (b + 1) = a * b + a := by simp [UInt128.mul_add]

-- protected theorem UInt128.succ_mul {a b : UInt128} : (a + 1) * b = a * b + b := by simp [UInt128.add_mul]

protected theorem UInt128.two_mul {a : UInt128} : 2 * a = a + a := UInt128.toBitVec_inj.1 BitVec.two_mul

protected theorem UInt128.mul_two {a : UInt128} : a * 2 = a + a := UInt128.toBitVec_inj.1 BitVec.mul_two

protected theorem UInt128.neg_mul (a b : UInt128) : -a * b = -(a * b) := UInt128.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem UInt128.mul_neg (a b : UInt128) : a * -b = -(a * b) := UInt128.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem UInt128.neg_mul_neg (a b : UInt128) : -a * -b = a * b := UInt128.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem UInt128.neg_mul_comm (a b : UInt128) : -a * b = a * -b := UInt128.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem UInt128.mul_sub {a b c : UInt128} : a * (b - c) = a * b - a * c := UInt128.toBitVec_inj.1 BitVec.mul_sub

protected theorem UInt128.sub_mul {a b c : UInt128} : (a - b) * c = a * c - b * c := by
  rw [UInt128.mul_comm, UInt128.mul_sub, UInt128.mul_comm, UInt128.mul_comm c]

theorem UInt128.neg_add_mul_eq_mul_not {a b : UInt128} : -(a + a * b) = a * ~~~b :=
  UInt128.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem UInt128.neg_mul_not_eq_add_mul {a b : UInt128} : -(a * ~~~b) = a + a * b :=
  UInt128.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem UInt128.le_of_lt {a b : UInt128} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt

protected theorem UInt128.lt_of_le_of_ne {a b : UInt128} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt128.toNat_inj] using Nat.lt_of_le_of_ne

protected theorem UInt128.lt_iff_le_and_ne {a b : UInt128} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt128.toNat_inj] using Nat.lt_iff_le_and_ne

protected theorem UInt128.div_self {a : UInt128} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt128.toBitVec_inj, apply_ite]

-- protected theorem UInt128.pos_iff_ne_zero {a : UInt128} : 0 < a ↔ a ≠ 0 := by simp [UInt128.lt_iff_le_and_ne, Eq.comm]

protected theorem UInt128.lt_of_le_of_lt {a b c : UInt128} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt

protected theorem UInt128.lt_of_lt_of_le {a b c : UInt128} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le

protected theorem UInt128.lt_or_lt_of_ne {a b : UInt128} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt128.toNat_inj] using Nat.lt_or_lt_of_ne

protected theorem UInt128.lt_or_le (a b : UInt128) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega

protected theorem UInt128.le_or_lt (a b : UInt128) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem UInt128.le_of_eq {a b : UInt128} : a = b → a ≤ b := (· ▸ UInt128.le_rfl)

protected theorem UInt128.le_iff_lt_or_eq {a b : UInt128} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt128.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq

protected theorem UInt128.lt_or_eq_of_le {a b : UInt128} : a ≤ b → a < b ∨ a = b := UInt128.le_iff_lt_or_eq.mp

protected theorem UInt128.sub_le {a b : UInt128} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt128.toNat_sub_of_le _ _ hab]

protected theorem UInt128.sub_lt {a b : UInt128} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt128.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt128.lt_iff_toNat_lt.1 hb)
  exact UInt128.lt_iff_toNat_lt.1 (UInt128.lt_of_lt_of_le hb hab)

theorem UInt128.lt_add_one {c : UInt128} (h : c ≠ -1) : c < c + 1 :=
  UInt128.lt_iff_toBitVec_lt.2 (BitVec.lt_add_one (by simpa [← UInt128.toBitVec_inj] using h))
