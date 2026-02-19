import Hax.rust_primitives.UInt128
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

-- Adapted from Lean/ToExpr.lean

open Lean in
instance : ToExpr Int128 where
  toTypeExpr := mkConst ``Int128
  toExpr i := if 0 ≤ i then
    mkNat i.toNatClampNeg
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``Int128 []) (.const ``Int128.instNeg [])
      (mkNat (-(i.toInt)).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int128 []) r
        (.app (.const ``Int128.instOfNat []) r)

-- Adapted from Lean/Meta/Tactic/Simp/BuiltinSimpProcs/SInt.lean

namespace Int128

open Lean Meta Simp

def fromExpr (e : Expr) : SimpM (Option Int128) := do
  if let some (n, _) ← getOfNatValue? e ``Int128 then
    return some (ofNat n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``Int128 | return none
  return some (ofInt (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Int128 → Int128 → Int128) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Int128 → Int128 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Int128 → Int128 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

open Lean Meta Simp in
dsimproc [simp, seval] reduceNeg ((- _ : Int128)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← (fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] reduceAdd ((_ + _ : Int128)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : Int128)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : Int128)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : Int128)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : Int128)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] reduceLT  (( _ : Int128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Int128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Int128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Int128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Int128) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Int128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : Int128) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : Int128) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfIntLE (ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity ``ofIntLE 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfInt (ofInt _) := fun e => do
  unless e.isAppOfArity ``ofInt 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToInt (toInt _) := fun e => do
  unless e.isAppOfArity ``toInt 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toInt v
  return .done <| toExpr n

dsimproc [simp, seval] reduceToNatClampNeg (toNatClampNeg _) := fun e => do
  unless e.isAppOfArity ``toNatClampNeg 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : Int128)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end Int128

-- Adapted from Init/Data/SInt/Lemmas.lean

declare_int_theorems Int128 128

theorem Int128.toInt.inj {x y : Int128} (h : x.toInt = y.toInt) : x = y := Int128.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem Int128.toInt_inj {x y : Int128} : x.toInt = y.toInt ↔ x = y := ⟨Int128.toInt.inj, fun h => h ▸ rfl⟩

@[simp, int_toBitVec] theorem Int128.toBitVec_neg (x : Int128) : (-x).toBitVec = -x.toBitVec := (rfl)
@[simp] theorem Int128.toBitVec_zero : toBitVec 0 = 0#128 := (rfl)

theorem Int128.toBitVec_one : (1 : Int128).toBitVec = 1#128 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem Int128.neg_zero : -(0 : Int128) = 0 := (rfl)

@[simp] theorem Int128.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int128.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

@[simp] theorem Int128.toInt_ofNat' {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int128.size := by
  rw [toInt, toBitVec_ofNat', BitVec.toInt_ofNat']

theorem Int128.toInt_ofNat {n : Nat} : toInt (no_index (OfNat.ofNat n)) = (n : Int).bmod Int128.size := by
  rw [toInt, toBitVec_ofNat, BitVec.toInt_ofNat]

theorem Int128.toInt_ofInt_of_le {n : Int} (hn : -2^127 ≤ n) (hn' : n < 2^127) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']

theorem Int128.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem Int128.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

theorem Int128.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem Int128.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 127) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]

theorem Int128.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 127) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]


theorem Int128.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2^127) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]

theorem Int128.toInt_zero : toInt 0 = 0 := by simp

theorem Int128.toInt_minValue : Int128.minValue.toInt = -2^127 := (rfl)

theorem Int128.toInt_maxValue : Int128.maxValue.toInt = 2 ^ 127 - 1 := (rfl)

@[simp] theorem Int128.toNatClampNeg_minValue : Int128.minValue.toNatClampNeg = 0 := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toInt128 (x : UInt128) : x.toInt128.toBitVec = x.toBitVec := (rfl)

@[simp] theorem Int128.ofBitVec_uInt128ToBitVec (x : UInt128) : Int128.ofBitVec x.toBitVec = x.toInt128 := (rfl)

@[simp] theorem UInt128.toUInt128_toInt128 (x : UInt128) : x.toInt128.toUInt128 = x := (rfl)

@[simp] theorem Int128.toNat_toInt (x : Int128) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem Int128.toInt_toBitVec (x : Int128) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem Int8.toBitVec_toInt128 (x : Int8) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)
@[simp, int_toBitVec] theorem Int16.toBitVec_toInt128 (x : Int16) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)
@[simp, int_toBitVec] theorem Int32.toBitVec_toInt128 (x : Int32) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)
@[simp, int_toBitVec] theorem Int128.toBitVec_toInt8 (x : Int128) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp, int_toBitVec] theorem Int128.toBitVec_toInt16 (x : Int128) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp, int_toBitVec] theorem Int128.toBitVec_toInt32 (x : Int128) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
-- @[simp, int_toBitVec] theorem Int128.toBitVec_toISize (x : Int128) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)
-- @[simp, int_toBitVec] theorem ISize.toBitVec_toInt128 (x : ISize) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)
theorem Int128.toInt_lt (x : Int128) : x.toInt < 2 ^ 127 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)
theorem Int128.le_toInt (x : Int128) : -2 ^ 127 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)
theorem Int128.toInt_le (x : Int128) : x.toInt ≤ Int128.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt
theorem Int128.minValue_le_toInt (x : Int128) : Int128.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize.int128MinValue_le_toInt (x : ISize) : Int128.minValue.toInt ≤ x.toInt :=
  Int.le_trans (by decide) x.le_toInt
theorem Int128.toNatClampNeg_lt (x : Int128) : x.toNatClampNeg < 2 ^ 127 := (Int.toNat_lt' (by decide)).2 x.toInt_lt
@[simp] theorem Int8.toInt_toInt128 (x : Int8) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int16.toInt_toInt128 (x : Int16) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int32.toInt_toInt128 (x : Int32) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int64.toInt_toInt128 (x : Int64) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int128.toInt_toInt8 (x : Int128) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int128.toInt_toInt16 (x : Int128) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int128.toInt_toInt32 (x : Int128) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
-- @[simp] theorem Int128.toInt_toISize (x : Int128) : x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
--   x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

-- @[simp] theorem ISize.toInt_toInt128 (x : ISize) : x.toInt128.toInt = x.toInt :=
--   x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int8.toNatClampNeg_toInt128 (x : Int8) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int16.toNatClampNeg_toInt128 (x : Int16) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int32.toNatClampNeg_toInt128 (x : Int32) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int64.toNatClampNeg_toInt128 (x : Int64) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

-- @[simp] theorem ISize.toNatClampNeg_toInt128 (x : ISize) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
--   congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int128.toInt128_toUInt128 (x : Int128) : x.toUInt128.toInt128 = x := (rfl)

theorem Int128.toNat_toBitVec (x : Int128) : x.toBitVec.toNat = x.toUInt128.toNat := (rfl)

theorem Int128.toNat_toBitVec_of_le {x : Int128} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem Int128.toNat_toUInt128_of_le {x : Int128} (hx : 0 ≤ x) : x.toUInt128.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

theorem Int128.toFin_toBitVec (x : Int128) : x.toBitVec.toFin = x.toUInt128.toFin := (rfl)
@[simp, int_toBitVec] theorem Int128.toBitVec_toUInt128 (x : Int128) : x.toUInt128.toBitVec = x.toBitVec := (rfl)
@[simp] theorem UInt128.ofBitVec_int128ToBitVec (x : Int128) : UInt128.ofBitVec x.toBitVec = x.toUInt128 := (rfl)
@[simp] theorem Int128.ofBitVec_toBitVec (x : Int128) : Int128.ofBitVec x.toBitVec = x := (rfl)
@[simp] theorem Int8.ofBitVec_int128ToBitVec (x : Int128) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)
@[simp] theorem Int16.ofBitVec_int128ToBitVec (x : Int128) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)
@[simp] theorem Int32.ofBitVec_int128ToBitVec (x : Int128) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)
@[simp] theorem Int64.ofBitVec_int128ToBitVec (x : Int128) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)
@[simp] theorem Int128.ofBitVec_int8ToBitVec (x : Int8) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofBitVec_int16ToBitVec (x : Int16) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofBitVec_int32ToBitVec (x : Int32) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofBitVec_int64ToBitVec (x : Int64) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)
-- @[simp] theorem Int128.ofBitVec_iSizeToBitVec (x : ISize) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)
-- @[simp] theorem ISize.ofBitVec_int128ToBitVec (x : Int128) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)
@[simp] theorem Int128.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int128.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 128 x := (rfl)
@[simp] theorem Int128.toInt_bmod (x : Int128) : x.toInt.bmod 340282366920938463463374607431768211456 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt

-- @[simp] theorem Int128.toInt_bmod_18446744073709551616 (x : Int128) : x.toInt.bmod 18446744073709551616 = x.toInt :=
--   Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem BitVec.ofInt_int128ToInt (x : Int128) : BitVec.ofInt 128 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)
@[simp] theorem Int128.ofIntLE_toInt (x : Int128) : Int128.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int128.toBitVec.inj (by simp)
theorem Int8.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)
theorem Int16.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)
theorem Int32.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int32.ofIntLE x.toInt h₁ h₂ = x.toInt32 := (rfl)
theorem Int64.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int64.ofIntLE x.toInt h₁ h₂ = x.toInt64 := (rfl)

@[simp] theorem Int128.ofIntLE_int8ToInt (x : Int8) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofIntLE_int16ToInt (x : Int16) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofIntLE_int32ToInt (x : Int32) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)
@[simp] theorem Int128.ofIntLE_int64ToInt (x : Int64) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)
-- @[simp] theorem Int128.ofIntLE_iSizeToInt (x : ISize) :
--     Int128.ofIntLE x.toInt x.int128MinValue_le_toInt x.toInt_le_int128MaxValue = x.toInt128 := (rfl)
-- theorem ISize.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : ISize.ofIntLE x.toInt h₁ h₂ = x.toISize := (rfl)
@[simp] theorem Int128.ofInt_toInt (x : Int128) : Int128.ofInt x.toInt = x := Int128.toBitVec.inj (by simp)
@[simp] theorem Int8.ofInt_int128ToInt (x : Int128) : Int8.ofInt x.toInt = x.toInt8 := (rfl)
@[simp] theorem Int16.ofInt_int128ToInt (x : Int128) : Int16.ofInt x.toInt = x.toInt16 := (rfl)
@[simp] theorem Int32.ofInt_int128ToInt (x : Int128) : Int32.ofInt x.toInt = x.toInt32 := (rfl)
@[simp] theorem Int64.ofInt_int128ToInt (x : Int128) : Int64.ofInt x.toInt = x.toInt64 := (rfl)
@[simp] theorem Int128.ofInt_int8ToInt (x : Int8) : Int128.ofInt x.toInt = x.toInt128 := (rfl)
@[simp] theorem Int128.ofInt_int16ToInt (x : Int16) : Int128.ofInt x.toInt = x.toInt128 := (rfl)
@[simp] theorem Int128.ofInt_int32ToInt (x : Int32) : Int128.ofInt x.toInt = x.toInt128 := (rfl)
@[simp] theorem Int128.ofInt_int64ToInt (x : Int64) : Int128.ofInt x.toInt = x.toInt128 := (rfl)
-- @[simp] theorem Int128.ofInt_iSizeToInt (x : ISize) : Int128.ofInt x.toInt = x.toInt128 := (rfl)
-- @[simp] theorem ISize.ofInt_int128ToInt (x : Int128) : ISize.ofInt x.toInt = x.toISize := (rfl)
@[simp] theorem Int128.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
theorem Int128.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]
theorem Int128.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int128.ofIntLE n h₁ h₂ = Int128.ofInt n := (rfl)
theorem Int128.toInt_ofIntTruncate {x : Int} (h₁ : Int128.minValue.toInt ≤ x)
    (h₂ : x ≤ Int128.maxValue.toInt) : (Int128.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]
@[simp] theorem Int128.ofIntTruncate_toInt (x : Int128) : Int128.ofIntTruncate x.toInt = x :=
  Int128.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)
@[simp] theorem Int128.ofIntTruncate_int8ToInt (x : Int8) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int128.ofIntTruncate_int16ToInt (x : Int16) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int128.ofIntTruncate_int32ToInt (x : Int32) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int128.ofIntTruncate_int64ToInt (x : Int64) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int64.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
-- @[simp] theorem Int128.ofIntTruncate_iSizeToInt (x : ISize) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
--   Int128.toInt.inj (by
--     rw [toInt_ofIntTruncate, ISize.toInt_toInt128]
--     · exact x.int128MinValue_le_toInt
--     · exact x.toInt_le_int128MaxValue)
theorem Int128.le_iff_toInt_le {x y : Int128} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le
theorem Int128.lt_iff_toInt_lt {x y : Int128} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt
theorem Int128.cast_toNatClampNeg (x : Int128) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]
theorem Int128.ofNat_toNatClampNeg (x : Int128) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])
theorem Int128.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toInt128])
theorem Int128.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toInt128])
theorem Int128.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toInt128])
@[simp] theorem Int8.toInt8_toInt128 (n : Int8) : n.toInt128.toInt8 = n :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int8.toInt16_toInt128 (n : Int8) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int8.toInt32_toInt128 (n : Int8) : n.toInt128.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)
@[simp] theorem Int8.toInt128_toInt16 (n : Int8) : n.toInt16.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)
@[simp] theorem Int8.toInt128_toInt32 (n : Int8) : n.toInt32.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)
-- @[simp] theorem Int8.toInt128_toISize (n : Int8) : n.toISize.toInt128 = n.toInt128 :=
--   Int128.toInt.inj (by simp)
-- @[simp] theorem Int8.toISize_toInt128 (n : Int8) : n.toInt128.toISize = n.toISize :=
--   ISize.toInt.inj (by simp)
@[simp] theorem Int16.toInt8_toInt128 (n : Int16) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int16.toInt16_toInt128 (n : Int16) : n.toInt128.toInt16 = n :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_toInt128 (n : Int16) : n.toInt128.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int16.toInt128_toInt32 (n : Int16) : n.toInt32.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)
-- @[simp] theorem Int16.toInt128_toISize (n : Int16) : n.toISize.toInt128 = n.toInt128 :=
--   Int128.toInt.inj (by simp)

-- @[simp] theorem Int16.toISize_toInt128 (n : Int16) : n.toInt128.toISize = n.toISize :=
--   ISize.toInt.inj (by simp)
@[simp] theorem Int32.toInt8_toInt128 (n : Int32) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int32.toInt16_toInt128 (n : Int32) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int32.toInt32_toInt128 (n : Int32) : n.toInt128.toInt32 = n :=
  Int32.toInt.inj (by simp)

-- @[simp] theorem Int32.toInt128_toISize (n : Int32) : n.toISize.toInt128 = n.toInt128 :=
--   Int128.toInt.inj (by simp)

-- @[simp] theorem Int32.toISize_toInt128 (n : Int32) : n.toInt128.toISize = n.toISize :=
--   ISize.toInt.inj (by simp)

@[simp] theorem Int64.toInt8_toInt128 (n : Int64) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int64.toInt16_toInt128 (n : Int64) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

-- @[simp] theorem Int64.toInt128_toISize (n : Int64) : n.toISize.toInt128 = n.toInt128 :=
--   Int128.toInt.inj (by simp)

-- @[simp] theorem Int64.toISize_toInt128 (n : Int64) : n.toInt128.toISize = n.toISize :=
--   ISize.toInt.inj (by simp)

@[simp] theorem Int128.toInt8_toInt16 (n : Int128) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int128.toInt8_toInt32 (n : Int128) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
-- @[simp] theorem Int128.toInt8_toInt64 (n : Int128) : n.toInt64.toInt8 = n.toInt8 :=
--   Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
-- @[simp] theorem Int128.toInt8_toISize (n : Int128) : n.toISize.toInt8 = n.toInt8 :=
--   Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem Int128.toInt16_toInt32 (n : Int128) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
-- @[simp] theorem Int128.toInt16_toISize (n : Int128) : n.toISize.toInt16 = n.toInt16 :=
--   Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

-- @[simp] theorem Int128.toInt32_toISize (n : Int128) : n.toISize.toInt32 = n.toInt32 :=
--   Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))
-- @[simp] theorem ISize.toInt8_toInt128 (n : ISize) : n.toInt128.toInt8 = n.toInt8 :=
--   Int8.toInt.inj (by simp)
-- @[simp] theorem ISize.toInt16_toInt128 (n : ISize) : n.toInt128.toInt16 = n.toInt16 :=
--   Int16.toInt.inj (by simp)

-- @[simp] theorem ISize.toInt32_toInt128 (n : ISize) : n.toInt128.toInt32 = n.toInt32 :=
--   Int32.toInt.inj (by simp)

-- @[simp] theorem ISize.toISize_toInt128 (n : ISize) : n.toInt128.toISize = n :=
--   ISize.toInt.inj (by simp)
-- theorem UInt128.toInt128_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toInt128 = Int128.ofNat n :=
--   Int128.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
@[simp] theorem UInt128.toInt128_ofNat' {n : Nat} : (UInt128.ofNat n).toInt128 = Int128.ofNat n := (rfl)
@[simp] theorem UInt128.toInt128_ofNat {n : Nat} : toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)
@[simp] theorem UInt128.toInt128_ofBitVec (b) : (UInt128.ofBitVec b).toInt128 = Int128.ofBitVec b := (rfl)
@[simp, int_toBitVec] theorem Int128.toBitVec_ofBitVec (b) : (Int128.ofBitVec b).toBitVec = b := (rfl)
theorem Int128.toBitVec_ofIntTruncate {n : Int} (h₁ : Int128.minValue.toInt ≤ n) (h₂ : n ≤ Int128.maxValue.toInt) :
    (Int128.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]
@[simp] theorem Int128.toInt_ofBitVec (b) : (Int128.ofBitVec b).toInt = b.toInt := (rfl)
@[simp] theorem Int128.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int128.toNatClampNeg_ofBitVec (b) : (Int128.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)
theorem Int128.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem Int128.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 63) :
    (Int128.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
@[simp] theorem Int128.toUInt128_ofBitVec (b) : (Int128.ofBitVec b).toUInt128 = UInt128.ofBitVec b := (rfl)
@[simp] theorem Int128.toUInt128_ofNat' {n} : (Int128.ofNat n).toUInt128 = UInt128.ofNat n := (rfl)
@[simp] theorem Int128.toUInt128_ofNat {n} : toUInt128 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)
theorem Int128.toInt8_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)
@[simp] theorem Int128.toInt8_ofBitVec (b) : (Int128.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int128.toInt8_ofNat' {n} : (Int128.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem Int128.toInt8_ofInt {n} : (Int128.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int128.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'
theorem Int128.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]
theorem Int128.toInt16_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)
@[simp] theorem Int128.toInt16_ofBitVec (b) : (Int128.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int128.toInt16_ofNat' {n} : (Int128.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem Int128.toInt16_ofInt {n} : (Int128.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int128.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'
theorem Int128.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]
theorem Int128.toInt32_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)

@[simp] theorem Int128.toInt32_ofBitVec (b) : (Int128.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int128.toInt32_ofNat' {n} : (Int128.ofNat n).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int128.toInt32_ofInt {n} : (Int128.ofInt n).toInt32 = Int32.ofInt n :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'

theorem Int128.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt32_ofIntLE]

-- theorem Int128.toISize_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toISize = ISize.ofInt n :=
--   ISize.toInt.inj (by simp [ISize.toInt_ofInt])

-- @[simp] theorem Int128.toISize_ofBitVec (b) : (Int128.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

-- @[simp] theorem Int128.toISize_ofNat' {n} : (Int128.ofNat n).toISize = ISize.ofNat n :=
--   ISize.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

-- @[simp] theorem Int128.toISize_ofInt {n} : (Int128.ofInt n).toISize = ISize.ofInt n :=
--  ISize.toInt.inj (by simpa [ISize.toInt_ofInt] using Int.bmod_bmod_of_dvd USize.size_dvd_uInt128Size)

-- @[simp] theorem Int128.toISize_ofNat {n} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize_ofNat'

-- theorem Int128.toISize_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
--     (Int128.ofIntTruncate n).toISize = ISize.ofInt n := by
--   rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize_ofIntLE]

@[simp, int_toBitVec] theorem Int128.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_maxValue : maxValue.toBitVec = BitVec.intMax _ := (rfl)

@[simp] theorem Int128.toInt8_neg (x : Int128) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)
@[simp] theorem Int128.toInt16_neg (x : Int128) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)

@[simp] theorem Int128.toInt32_neg (x : Int128) : (-x).toInt32 = -x.toInt32 := Int32.toBitVec.inj (by simp)

-- @[simp] theorem Int128.toISize_neg (x : Int128) : (-x).toISize = -x.toISize := ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.toInt128_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))
@[simp] theorem Int16.toInt128_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))
@[simp] theorem Int32.toInt128_neg_of_ne {x : Int32} (hx : x ≠ -2147483648) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (Int32.toBitVec.inj h)))
@[simp] theorem Int64.toInt128_neg_of_ne {x : Int64} (hx : x ≠ -9223372036854775808) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (Int64.toBitVec.inj h)))
-- @[simp] theorem ISize.toInt128_neg_of_ne {x : ISize} (hx : x ≠ minValue) : (-x).toInt128 = -x.toInt128 :=
--   Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _
--     (fun h => hx (ISize.toBitVec.inj (h.trans toBitVec_minValue.symm))))

theorem Int8.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)
@[simp] theorem Int8.toInt128_ofBitVec (b) : (Int8.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int8.toInt128_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]
@[simp] theorem Int8.toInt128_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp) h, Int128.ofInt_eq_ofNat]
@[simp] theorem Int8.toInt128_ofNat {n : Nat} (h : n ≤ 127) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toInt128_ofNat' (by rw [toInt_maxValue]; omega)
theorem Int16.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)
@[simp] theorem Int16.toInt128_ofBitVec (b) : (Int16.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int16.toInt128_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]
@[simp] theorem Int16.toInt128_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp) h, Int128.ofInt_eq_ofNat]
@[simp] theorem Int16.toInt128_ofNat {n : Nat} (h : n ≤ 32767) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toInt128_ofNat' (by rw [toInt_maxValue]; omega)
theorem Int32.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int32.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int32.toInt128_ofBitVec (b) : (Int32.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int32.toInt128_ofInt {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int32.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int32.toInt128_ofNat' {n : Nat} (h : n ≤ Int32.maxValue.toInt) :
    (Int32.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp) h, Int128.ofInt_eq_ofNat]

@[simp] theorem Int32.toInt128_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int32.toInt128_ofNat' (by rw [toInt_maxValue]; omega)

-- theorem ISize.toInt128_ofIntLE {n : Int} (h₁ h₂) :
--     (ISize.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans minValue.int128MinValue_le_toInt h₁)
--       (Int.le_trans h₂ maxValue.toInt_le_int128MaxValue) :=
--   Int128.toInt.inj (by simp)

-- @[simp] theorem ISize.toInt128_ofBitVec (b) : (ISize.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

-- @[simp] theorem ISize.toInt128_ofInt {n : Int} (h₁ : ISize.minValue.toInt ≤ n) (h₂ : n ≤ ISize.maxValue.toInt) :
--     (ISize.ofInt n).toInt128 = Int128.ofInt n := by rw [← ISize.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

-- @[simp] theorem ISize.toInt128_ofNat' {n : Nat} (h : n ≤ ISize.maxValue.toInt) :
--     (ISize.ofNat n).toInt128 = Int128.ofNat n := by
--   rw [← ofInt_eq_ofNat, toInt128_ofInt _ h, Int128.ofInt_eq_ofNat]
--   refine Int.le_trans ?_ (Int.zero_le_ofNat _)
--   cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue]

-- @[simp] theorem ISize.toInt128_ofNat {n : Nat} (h : n ≤ 2147483647) :
--     toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
--   ISize.toInt128_ofNat' (by rw [toInt_maxValue]; cases System.Platform.numBits_eq <;> simp_all <;> omega)
@[simp] theorem Int128.ofIntLE_bitVecToInt (n : BitVec 128) :
    Int128.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)

theorem Int128.ofBitVec_ofNatLT (n : Nat) (hn) : Int128.ofBitVec (BitVec.ofNatLT n hn) = Int128.ofNat n :=
  Int128.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])
@[simp] theorem Int128.ofBitVec_ofNat (n : Nat) : Int128.ofBitVec (BitVec.ofNat 128 n) = Int128.ofNat n := (rfl)
@[simp] theorem Int128.ofBitVec_ofInt (n : Int) : Int128.ofBitVec (BitVec.ofInt 128 n) = Int128.ofInt n := (rfl)
@[simp] theorem Int128.ofNat_bitVecToNat (n : BitVec 128) : Int128.ofNat n.toNat = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)
@[simp] theorem Int128.ofInt_bitVecToInt (n : BitVec 128) : Int128.ofInt n.toInt = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)
@[simp] theorem Int128.ofIntTruncate_bitVecToInt (n : BitVec 128) : Int128.ofIntTruncate n.toInt = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])
@[simp] theorem Int128.toInt_neg (n : Int128) : (-n).toInt = (-n.toInt).bmod (2 ^ 128) := BitVec.toInt_neg
@[simp] theorem Int128.toNatClampNeg_eq_zero_iff {n : Int128} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]
@[simp] protected theorem Int128.not_le {n m : Int128} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] theorem Int128.neg_nonpos_iff (n : Int128) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]
@[simp] theorem Int128.toNatClampNeg_pos_iff (n : Int128) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int128.toInt_div (a b : Int128) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]
theorem Int128.toInt_div_of_ne_left (a b : Int128) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)
theorem Int128.toInt_div_of_ne_right (a b : Int128) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)
theorem Int8.toInt128_ne_minValue (a : Int8) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega
theorem Int16.toInt128_ne_minValue (a : Int16) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega
theorem Int32.toInt128_ne_minValue (a : Int32) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega
-- theorem ISize.toInt128_ne_minValue (a : ISize) (ha : a ≠ minValue) : a.toInt128 ≠ Int128.minValue := by
--   have := a.minValue_le_toInt
--   have : -2 ^ 127 ≤ minValue.toInt := minValue.le_toInt
--   simp [← Int128.toInt_inj, ← ISize.toInt_inj] at *; omega

theorem Int8.toInt128_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt8 (by simpa using ha)
theorem Int16.toInt128_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt16 (by simpa using ha)
theorem Int32.toInt128_ne_neg_one (a : Int32) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt32 (by simpa using ha)
-- theorem ISize.toInt128_ne_neg_one (a : ISize) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
--   ne_of_apply_ne Int128.toISize (by simpa using ha)

theorem Int8.toInt128_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])
theorem Int16.toInt128_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])
theorem Int32.toInt128_div_of_ne_left (a b : Int32) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])
-- theorem ISize.toInt128_div_of_ne_left (a b : ISize) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
--   Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    -- Int128.toInt_div_of_ne_left _ _ (a.toInt128_ne_minValue ha), toInt_toInt128, toInt_toInt128])
theorem Int8.toInt128_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])
theorem Int16.toInt128_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])
theorem Int32.toInt128_div_of_ne_right (a b : Int32) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])
-- theorem ISize.toInt128_div_of_ne_right (a b : ISize) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
--   Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
--     Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])
@[simp] theorem Int128.minValue_div_neg_one : minValue / -1 = minValue := by decide
@[simp] theorem Int128.toInt_add (a b : Int128) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int128.toInt8_add (a b : Int128) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int128.toInt16_add (a b : Int128) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int128.toInt32_add (a b : Int128) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
-- @[simp] theorem Int128.toISize_add (a b : Int128) : (a + b).toISize = a.toISize + b.toISize :=
--   ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int128.toInt_mul (a b : Int128) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int128.toInt8_mul (a b : Int128) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int128.toInt16_mul (a b : Int128) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int128.toInt32_mul (a b : Int128) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
-- @[simp] theorem Int128.toISize_mul (a b : Int128) : (a * b).toISize = a.toISize * b.toISize :=
--   ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
protected theorem Int128.sub_eq_add_neg (a b : Int128) : a - b = a + -b := Int128.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])
@[simp] theorem Int128.toInt_sub (a b : Int128) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 128) := by
  simp [Int128.sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem Int128.toInt8_sub (a b : Int128) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [Int128.sub_eq_add_neg, Int8.sub_eq_add_neg]
@[simp] theorem Int128.toInt16_sub (a b : Int128) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [Int128.sub_eq_add_neg, Int16.sub_eq_add_neg]
@[simp] theorem Int128.toInt32_sub (a b : Int128) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [Int128.sub_eq_add_neg, Int32.sub_eq_add_neg]
-- @[simp] theorem Int128.toISize_sub (a b : Int128) : (a - b).toISize = a.toISize - b.toISize := by
--   simp [Int128.sub_eq_add_neg, ISize.sub_eq_add_neg]
@[simp] theorem Int8.toInt128_lt {a b : Int8} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]
@[simp] theorem Int16.toInt128_lt {a b : Int16} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]
@[simp] theorem Int32.toInt128_lt {a b : Int32} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]
-- @[simp] theorem ISize.toInt128_lt {a b : ISize} : a.toInt128 < b.toInt128 ↔ a < b := by
--   simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]

@[simp] theorem Int8.toInt128_le {a b : Int8} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]
@[simp] theorem Int16.toInt128_le {a b : Int16} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]
@[simp] theorem Int32.toInt128_le {a b : Int32} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]
-- @[simp] theorem ISize.toInt128_le {a b : ISize} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
--   simp [le_iff_toInt_le, Int128.le_iff_toInt_le]
@[simp] theorem Int128.ofBitVec_neg (a : BitVec 128) : Int128.ofBitVec (-a) = -Int128.ofBitVec a := (rfl)
@[simp] theorem Int128.ofInt_neg (a : Int) : Int128.ofInt (-a) = -Int128.ofInt a := Int128.toInt_inj.1 (by simp)
theorem Int128.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int128) : Int128.ofInt a = b ↔ a.bmod (2 ^ 128) = b.toInt := by
  simp [← Int128.toInt_inj]
@[simp] theorem Int128.ofBitVec_add (a b : BitVec 128) : Int128.ofBitVec (a + b) = Int128.ofBitVec a + Int128.ofBitVec b := (rfl)
@[simp] theorem Int128.ofInt_add (a b : Int) : Int128.ofInt (a + b) = Int128.ofInt a + Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int128.ofNat_add (a b : Nat) : Int128.ofNat (a + b) = Int128.ofNat a + Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat]
theorem Int128.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a + b) hab₁ hab₂ = Int128.ofInt a + Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]
@[simp] theorem Int128.ofBitVec_sub (a b : BitVec 128) : Int128.ofBitVec (a - b) = Int128.ofBitVec a - Int128.ofBitVec b := (rfl)
@[simp] theorem Int128.ofInt_sub (a b : Int) : Int128.ofInt (a - b) = Int128.ofInt a - Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int128.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int128.ofNat (a - b) = Int128.ofNat a - Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat, Int.ofNat_sub hab]
theorem Int128.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a - b) hab₁ hab₂ = Int128.ofInt a - Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]
@[simp] theorem Int128.ofBitVec_mul (a b : BitVec 128) : Int128.ofBitVec (a * b) = Int128.ofBitVec a * Int128.ofBitVec b := (rfl)
@[simp] theorem Int128.ofInt_mul (a b : Int) : Int128.ofInt (a * b) = Int128.ofInt a * Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int128.ofNat_mul (a b : Nat) : Int128.ofNat (a * b) = Int128.ofNat a * Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat]
theorem Int128.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a * b) hab₁ hab₂ = Int128.ofInt a * Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]
theorem Int128.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide
theorem Int128.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 127 := (rfl)
@[simp] theorem Int128.ofBitVec_sdiv (a b : BitVec 128) : Int128.ofBitVec (a.sdiv b) = Int128.ofBitVec a / Int128.ofBitVec b := (rfl)
theorem Int128.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt (a.tdiv b) = Int128.ofInt a / Int128.ofInt b := by
  rw [Int128.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int128.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofInt (a.tdiv b) = Int128.ofIntLE a ha₁ ha₂ / Int128.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]
theorem Int128.ofNat_div {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat (a / b) = Int128.ofNat a / Int128.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
@[simp] theorem Int128.ofBitVec_srem (a b : BitVec 128) : Int128.ofBitVec (a.srem b) = Int128.ofBitVec a % Int128.ofBitVec b := (rfl)
@[simp] theorem Int128.toInt_bmod_size (a : Int128) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _
theorem Int128.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofIntLE a ha₁ ha₂ ≤ Int128.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]
theorem Int128.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt a ≤ Int128.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]
theorem Int128.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat a ≤ Int128.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int128.ofBitVec_le_iff_sle (a b : BitVec 128) : Int128.ofBitVec a ≤ Int128.ofBitVec b ↔ a.sle b := Iff.rfl
theorem Int128.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofIntLE a ha₁ ha₂ < Int128.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]
theorem Int128.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt a < Int128.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]
theorem Int128.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat a < Int128.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)
theorem Int128.ofBitVec_lt_iff_slt (a b : BitVec 128) : Int128.ofBitVec a < Int128.ofBitVec b ↔ a.slt b := Iff.rfl
theorem Int128.toNatClampNeg_one : (1 : Int128).toNatClampNeg = 1 := (rfl)
theorem Int128.toInt_one : (1 : Int128).toInt = 1 := (rfl)
theorem Int128.zero_lt_one : (0 : Int128) < 1 := by decide
theorem Int128.zero_ne_one : (0 : Int128) ≠ 1 := by decide
protected theorem Int128.add_assoc (a b c : Int128) : a + b + c = a + (b + c) :=
  Int128.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
instance : Std.Associative (α := Int128) (· + ·) := ⟨Int128.add_assoc⟩
protected theorem Int128.add_comm (a b : Int128) : a + b = b + a := Int128.toBitVec_inj.1 (BitVec.add_comm _ _)
instance : Std.Commutative (α := Int128) (· + ·) := ⟨Int128.add_comm⟩
@[simp] protected theorem Int128.add_zero (a : Int128) : a + 0 = a := Int128.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem Int128.zero_add (a : Int128) : 0 + a = a := Int128.toBitVec_inj.1 (BitVec.zero_add _)
instance : Std.LawfulIdentity (α := Int128) (· + ·) 0 where
  left_id := Int128.zero_add
  right_id := Int128.add_zero
@[simp] protected theorem Int128.sub_zero (a : Int128) : a - 0 = a := Int128.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem Int128.zero_sub (a : Int128) : 0 - a = -a := Int128.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem Int128.sub_self (a : Int128) : a - a = 0 := Int128.toBitVec_inj.1 (BitVec.sub_self _)
protected theorem Int128.add_left_neg (a : Int128) : -a + a = 0 := Int128.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem Int128.add_right_neg (a : Int128) : a + -a = 0 := Int128.toBitVec_inj.1 (BitVec.add_right_neg _)
@[simp] protected theorem Int128.sub_add_cancel (a b : Int128) : a - b + b = a :=
  Int128.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
protected theorem Int128.eq_sub_iff_add_eq {a b c : Int128} : a = c - b ↔ a + b = c := by
  simpa [← Int128.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem Int128.sub_eq_iff_eq_add {a b c : Int128} : a - b = c ↔ a = c + b := by
  simpa [← Int128.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
@[simp] protected theorem Int128.neg_neg {a : Int128} : - -a = a := Int128.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem Int128.neg_inj {a b : Int128} : -a = -b ↔ a = b := by simp [← Int128.toBitVec_inj]
@[simp] protected theorem Int128.neg_ne_zero {a : Int128} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int128.toBitVec_inj]
protected theorem Int128.neg_add {a b : Int128} : - (a + b) = -a - b := Int128.toBitVec_inj.1 BitVec.neg_add
@[simp] protected theorem Int128.sub_neg {a b : Int128} : a - -b = a + b := Int128.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem Int128.neg_sub {a b : Int128} : -(a - b) = b - a := by
  rw [Int128.sub_eq_add_neg, Int128.neg_add, Int128.sub_neg, Int128.add_comm, ← Int128.sub_eq_add_neg]
protected theorem Int128.sub_sub (a b c : Int128) : a - b - c = a - (b + c) := by
  simp [Int128.sub_eq_add_neg, Int128.add_assoc, Int128.neg_add]
@[simp] protected theorem Int128.add_left_inj {a b : Int128} (c : Int128) : (a + c = b + c) ↔ a = b := by
  simp [← Int128.toBitVec_inj]
@[simp] protected theorem Int128.add_right_inj {a b : Int128} (c : Int128) : (c + a = c + b) ↔ a = b := by
  simp [← Int128.toBitVec_inj]
@[simp] protected theorem Int128.sub_left_inj {a b : Int128} (c : Int128) : (a - c = b - c) ↔ a = b := by
  simp [← Int128.toBitVec_inj]
@[simp] protected theorem Int128.sub_right_inj {a b : Int128} (c : Int128) : (c - a = c - b) ↔ a = b := by
  simp [← Int128.toBitVec_inj]
@[simp] theorem Int128.add_eq_right {a b : Int128} : a + b = b ↔ a = 0 := by
  simp [← Int128.toBitVec_inj]
@[simp] theorem Int128.add_eq_left {a b : Int128} : a + b = a ↔ b = 0 := by
  simp [← Int128.toBitVec_inj]
@[simp] theorem Int128.right_eq_add {a b : Int128} : b = a + b ↔ a = 0 := by
  simp [← Int128.toBitVec_inj]
@[simp] theorem Int128.left_eq_add {a b : Int128} : a = a + b ↔ b = 0 := by
  simp [← Int128.toBitVec_inj]
protected theorem Int128.mul_comm (a b : Int128) : a * b = b * a := Int128.toBitVec_inj.1 (BitVec.mul_comm _ _)
instance : Std.Commutative (α := Int128) (· * ·) := ⟨Int128.mul_comm⟩
protected theorem Int128.mul_assoc (a b c : Int128) : a * b * c = a * (b * c) := Int128.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
instance : Std.Associative (α := Int128) (· * ·) := ⟨Int128.mul_assoc⟩
@[simp] theorem Int128.mul_one (a : Int128) : a * 1 = a := Int128.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem Int128.one_mul (a : Int128) : 1 * a = a := Int128.toBitVec_inj.1 (BitVec.one_mul _)
instance : Std.LawfulCommIdentity (α := Int128) (· * ·) 1 where
  right_id := Int128.mul_one
@[simp] theorem Int128.mul_zero {a : Int128} : a * 0 = 0 := Int128.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem Int128.zero_mul {a : Int128} : 0 * a = 0 := Int128.toBitVec_inj.1 BitVec.zero_mul
@[simp] protected theorem Int128.pow_zero (x : Int128) : x ^ 0 = 1 := (rfl)
protected theorem Int128.pow_succ (x : Int128) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)
protected theorem Int128.mul_add {a b c : Int128} : a * (b + c) = a * b + a * c :=
    Int128.toBitVec_inj.1 BitVec.mul_add
protected theorem Int128.add_mul {a b c : Int128} : (a + b) * c = a * c + b * c := by
  rw [Int128.mul_comm, Int128.mul_add, Int128.mul_comm a c, Int128.mul_comm c b]
protected theorem Int128.mul_succ {a b : Int128} : a * (b + 1) = a * b + a := by simp [Int128.mul_add]
protected theorem Int128.succ_mul {a b : Int128} : (a + 1) * b = a * b + b := by simp [Int128.add_mul]
protected theorem Int128.two_mul {a : Int128} : 2 * a = a + a := Int128.toBitVec_inj.1 BitVec.two_mul
protected theorem Int128.mul_two {a : Int128} : a * 2 = a + a := Int128.toBitVec_inj.1 BitVec.mul_two
protected theorem Int128.neg_mul (a b : Int128) : -a * b = -(a * b) := Int128.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem Int128.mul_neg (a b : Int128) : a * -b = -(a * b) := Int128.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem Int128.neg_mul_neg (a b : Int128) : -a * -b = a * b := Int128.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem Int128.neg_mul_comm (a b : Int128) : -a * b = a * -b := Int128.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem Int128.mul_sub {a b c : Int128} : a * (b - c) = a * b - a * c := Int128.toBitVec_inj.1 BitVec.mul_sub
protected theorem Int128.sub_mul {a b c : Int128} : (a - b) * c = a * c - b * c := by
  rw [Int128.mul_comm, Int128.mul_sub, Int128.mul_comm, Int128.mul_comm c]
theorem Int128.neg_add_mul_eq_mul_not {a b : Int128} : -(a + a * b) = a * ~~~b :=
  Int128.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem Int128.neg_mul_not_eq_add_mul {a b : Int128} : -(a * ~~~b) = a + a * b :=
  Int128.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
protected theorem Int128.le_of_lt {a b : Int128} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt
protected theorem Int128.lt_of_le_of_ne {a b : Int128} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int128.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)
protected theorem Int128.lt_iff_le_and_ne {a b : Int128} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int128.toInt_inj] using Int.lt_iff_le_and_ne
@[simp] protected theorem Int128.lt_irrefl {a : Int128} : ¬a < a := by simp [lt_iff_toInt_lt]
protected theorem Int128.lt_of_le_of_lt {a b c : Int128} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt
protected theorem Int128.lt_of_lt_of_le {a b c : Int128} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le
@[simp] theorem Int128.minValue_le (a : Int128) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem Int128.le_maxValue (a : Int128) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le
@[simp] theorem Int128.not_lt_minValue {a : Int128} : ¬a < minValue :=
  fun h => Int128.lt_irrefl (Int128.lt_of_le_of_lt a.minValue_le h)
@[simp] theorem Int128.not_maxValue_lt {a : Int128} : ¬maxValue < a :=
  fun h => Int128.lt_irrefl (Int128.lt_of_lt_of_le h a.le_maxValue)
@[simp] protected theorem Int128.le_refl (a : Int128) : a ≤ a := by simp [Int128.le_iff_toInt_le]
protected theorem Int128.le_rfl {a : Int128} : a ≤ a := Int128.le_refl _
protected theorem Int128.le_antisymm_iff {a b : Int128} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int128.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩
protected theorem Int128.le_antisymm {a b : Int128} : a ≤ b → b ≤ a → a = b := by simpa using Int128.le_antisymm_iff.2
@[simp] theorem Int128.le_minValue_iff {a : Int128} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int128.le_antisymm h a.minValue_le, by rintro rfl; simp⟩
@[simp] theorem Int128.maxValue_le_iff {a : Int128} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int128.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩
set_option maxRecDepth 1000 in
@[simp] protected theorem Int128.zero_div {a : Int128} : 0 / a = 0 := Int128.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem Int128.div_zero {a : Int128} : a / 0 = 0 := Int128.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem Int128.div_one {a : Int128} : a / 1 = a := Int128.toBitVec_inj.1 BitVec.sdiv_one
protected theorem Int128.div_self {a : Int128} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int128.toBitVec_inj, apply_ite]
@[simp] protected theorem Int128.mod_zero {a : Int128} : a % 0 = a := Int128.toBitVec_inj.1 BitVec.srem_zero
set_option maxRecDepth 1000 in
@[simp] protected theorem Int128.zero_mod {a : Int128} : 0 % a = 0 := Int128.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem Int128.mod_one {a : Int128} : a % 1 = 0 := Int128.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem Int128.mod_self {a : Int128} : a % a = 0 := Int128.toBitVec_inj.1 BitVec.srem_self
@[simp] protected theorem Int128.not_lt {a b : Int128} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]
protected theorem Int128.le_trans {a b c : Int128} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans
protected theorem Int128.lt_trans {a b c : Int128} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans
protected theorem Int128.le_total (a b : Int128) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _
protected theorem Int128.lt_asymm {a b : Int128} : a < b → ¬b < a :=
  fun hab hba => Int128.lt_irrefl (Int128.lt_trans hab hba)

open Std in
instance Int128.instIsLinearOrder : IsLinearOrder Int128 := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply Int128.le_antisymm
  case le_total => constructor; apply Int128.le_total
  case le_trans => constructor; apply Int128.le_trans

open Std in
instance : LawfulOrderLT Int128 where
  lt_iff := by
    simp [← Int128.not_le, Decidable.imp_iff_not_or, Std.Total.total]

protected theorem Int128.add_neg_eq_sub {a b : Int128} : a + -b = a - b := Int128.toBitVec_inj.1 BitVec.add_neg_eq_sub
theorem Int128.neg_eq_neg_one_mul (a : Int128) : -a = -1 * a := Int128.toInt_inj.1 (by simp)
@[simp] protected theorem Int128.add_sub_cancel (a b : Int128) : a + b - b = a := Int128.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
protected theorem Int128.lt_or_lt_of_ne {a b : Int128} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int128.toInt_inj]; omega
protected theorem Int128.lt_or_le (a b : Int128) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem Int128.le_or_lt (a b : Int128) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem Int128.le_of_eq {a b : Int128} : a = b → a ≤ b := (· ▸ Int128.le_rfl)
protected theorem Int128.le_iff_lt_or_eq {a b : Int128} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int128.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem Int128.lt_or_eq_of_le {a b : Int128} : a ≤ b → a < b ∨ a = b := Int128.le_iff_lt_or_eq.mp
theorem Int128.toInt_eq_toNatClampNeg {a : Int128} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha
@[simp] theorem UInt128.toInt128_add (a b : UInt128) : (a + b).toInt128 = a.toInt128 + b.toInt128 := (rfl)
@[simp] theorem UInt128.toInt128_neg (a : UInt128) : (-a).toInt128 = -a.toInt128 := (rfl)
@[simp] theorem UInt128.toInt128_sub (a b : UInt128) : (a - b).toInt128 = a.toInt128 - b.toInt128 := (rfl)
@[simp] theorem UInt128.toInt128_mul (a b : UInt128) : (a * b).toInt128 = a.toInt128 * b.toInt128 := (rfl)
@[simp] theorem Int128.toUInt128_add (a b : Int128) : (a + b).toUInt128 = a.toUInt128 + b.toUInt128 := (rfl)
@[simp] theorem Int128.toUInt128_neg (a : Int128) : (-a).toUInt128 = -a.toUInt128 := (rfl)
@[simp] theorem Int128.toUInt128_sub (a b : Int128) : (a - b).toUInt128 = a.toUInt128 - b.toUInt128 := (rfl)
@[simp] theorem Int128.toUInt128_mul (a b : Int128) : (a * b).toUInt128 = a.toUInt128 * b.toUInt128 := (rfl)
theorem Int128.toNatClampNeg_le {a b : Int128} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int128.toNat_toInt, ← Int128.toNat_toInt]
  exact Int.toNat_le_toNat (Int128.le_iff_toInt_le.1 hab)
theorem Int128.toUInt128_le {a b : Int128} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt128 ≤ b.toUInt128 := by
  rw [UInt128.le_iff_toNat_le, toNat_toUInt128_of_le ha, toNat_toUInt128_of_le (Int128.le_trans ha hab)]
  exact Int128.toNatClampNeg_le hab
theorem Int128.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 127) : 0 ≤ Int128.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int128.toInt_zero]
  exact Int.natCast_nonneg _
protected theorem Int128.sub_nonneg_of_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int128.le_trans hb hab),
    ← ofNat_sub _ _ (Int128.toNatClampNeg_le hab)]
  exact Int128.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)
theorem Int128.toNatClampNeg_sub_of_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt128_of_le (Int128.sub_nonneg_of_le hb hab), toUInt128_sub,
    UInt128.toNat_sub_of_le _ _ (Int128.toUInt128_le hb hab),
    ← toNat_toUInt128_of_le (Int128.le_trans hb hab), ← toNat_toUInt128_of_le hb]
theorem Int128.toInt_sub_of_le (a b : Int128) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int128.toInt_eq_toNatClampNeg (Int128.sub_nonneg_of_le hb h),
    Int128.toInt_eq_toNatClampNeg (Int128.le_trans hb h), Int128.toInt_eq_toNatClampNeg hb,
    Int128.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int128.toNatClampNeg_le h
protected theorem Int128.sub_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int128.toInt_sub_of_le _ _ hb hab]; omega
protected theorem Int128.sub_lt {a b : Int128} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int128.toInt_sub_of_le _ _ (Int128.le_of_lt hb) hab]; omega
protected theorem Int128.ne_of_lt {a b : Int128} : a < b → a ≠ b := by
  simpa [Int128.lt_iff_toInt_lt, ← Int128.toInt_inj] using Int.ne_of_lt
@[simp] theorem Int128.toInt_mod (a b : Int128) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int8.toInt128_mod (a b : Int8) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)
@[simp] theorem Int16.toInt128_mod (a b : Int16) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)
@[simp] theorem Int32.toInt128_mod (a b : Int32) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)
@[simp] theorem Int64.toInt128_mod (a b : Int64) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)
-- @[simp] theorem ISize.toInt128_mod (a b : ISize) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)
theorem Int128.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt (a.tmod b) = Int128.ofInt a % Int128.ofInt b := by
  rw [Int128.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int128.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofInt (a.tmod b) = Int128.ofIntLE a ha₁ ha₂ % Int128.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]
theorem Int128.ofNat_mod {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat (a % b) = Int128.ofNat a % Int128.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
