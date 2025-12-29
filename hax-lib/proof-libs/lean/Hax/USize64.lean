import Hax.MissingLean
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt

/-!
# USize64

We define a type `USize64` to represent Rust's `usize` type. It is simply a copy of `UInt64`.
This file aims to collect all definitions, lemmas, and type class instances about `UInt64` from
Lean's standard library and to state them for `USize64`.
-/

/-- A copy of `UInt64`, which we use to represent Rust's `usize` type. -/
structure USize64 where ofUInt64 :: toUInt64 : UInt64

@[reducible] def USize64.size : Nat := UInt64.size
def USize64.ofNat (n : Nat) : USize64 := ⟨UInt64.ofNat n⟩
def USize64.toNat (n : USize64) : Nat := UInt64.toNat n.toUInt64
def USize64.ofBitVec (n : BitVec 64) : USize64 := ⟨UInt64.ofBitVec n⟩
def USize64.toBitVec (n : USize64) : BitVec 64 := UInt64.toBitVec n.toUInt64
def USize64.toFin (n : USize64) : Fin USize64.size := UInt64.toFin n.toUInt64

def USize64.ofNatLT (n : @& Nat) (h : LT.lt n USize64.size) : USize64 := ⟨UInt64.ofNatLT n h⟩

def USize64.decEq (a b : USize64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => USize64.noConfusion h' (fun h' => absurd h' h)))

abbrev Nat.toUSize64 := USize64.ofNat

namespace USize64

instance : DecidableEq USize64 := USize64.decEq

instance : Inhabited USize64 where
  default := USize64.ofNatLT 0 (of_decide_eq_true rfl)

instance {n} : OfNat USize64 n := ⟨⟨OfNat.ofNat n⟩⟩

end USize64

@[inline] def USize64.ofFin (a : Fin USize64.size) : USize64 := ⟨⟨a⟩⟩

def USize64.ofInt (x : Int) : USize64 := ofNat (x % 2 ^ 64).toNat

@[simp] theorem USize64.le_size : 2 ^ 32 ≤ USize64.size := by simp [USize64.size, UInt64.size]
@[simp] theorem USize64.size_le : USize64.size ≤ 2 ^ 64 := by simp [USize64.size, UInt64.size]

protected def USize64.add (a b : USize64) : USize64 := ⟨a.toUInt64 + b.toUInt64⟩
protected def USize64.sub (a b : USize64) : USize64 := ⟨a.toUInt64 - b.toUInt64⟩
protected def USize64.mul (a b : USize64) : USize64 := ⟨a.toUInt64 * b.toUInt64⟩
protected def USize64.div (a b : USize64) : USize64 := ⟨a.toUInt64 / b.toUInt64⟩
protected def USize64.pow (x : USize64) (n : Nat) : USize64 := ⟨x.toUInt64 ^ n⟩
protected def USize64.mod (a b : USize64) : USize64 := ⟨a.toUInt64 % b.toUInt64⟩

protected def USize64.land (a b : USize64) : USize64 := ⟨a.toUInt64 &&& b.toUInt64⟩
protected def USize64.lor (a b : USize64) : USize64 := ⟨a.toUInt64 ||| b.toUInt64⟩
protected def USize64.xor (a b : USize64) : USize64 := ⟨a.toUInt64 ^^^ b.toUInt64⟩
protected def USize64.shiftLeft (a b : USize64) : USize64 := ⟨a.toUInt64 <<< (USize64.mod b 64).toUInt64⟩
protected def USize64.shiftRight (a b : USize64) : USize64 := ⟨a.toUInt64 >>> (USize64.mod b 64).toUInt64⟩
protected def USize64.lt (a b : USize64) : Prop := a.toUInt64 < b.toUInt64
protected def USize64.le (a b : USize64) : Prop := a.toUInt64 ≤ b.toUInt64

instance : Add USize64       := ⟨USize64.add⟩
instance : Sub USize64       := ⟨USize64.sub⟩
instance : Mul USize64       := ⟨USize64.mul⟩
instance : Pow USize64 Nat   := ⟨USize64.pow⟩
instance : Mod USize64       := ⟨USize64.mod⟩

instance : HMod USize64 Nat USize64 := ⟨fun x n => ⟨x.toUInt64 % n⟩⟩

instance : Div USize64       := ⟨USize64.div⟩
instance : LT USize64        := ⟨USize64.lt⟩
instance : LE USize64        := ⟨USize64.le⟩

protected def USize64.complement (a : USize64) : USize64 := ⟨~~~a.toUInt64⟩
protected def USize64.neg (a : USize64) : USize64 := ⟨-a.toUInt64⟩

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
def UInt64.toUSize64 (a : UInt64) : USize64 := ⟨a⟩
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

theorem USize64.umulOverflow_iff (x y : USize64) :
    BitVec.umulOverflow x.toBitVec y.toBitVec ↔ x.toNat * y.toNat ≥ 2 ^ 64 :=
  UInt64.umulOverflow_iff _ _

theorem USize64.uaddOverflow_iff (x y : USize64) :
    BitVec.uaddOverflow x.toBitVec y.toBitVec ↔ x.toNat + y.toNat ≥ 2 ^ 64 :=
  UInt64.uaddOverflow_iff _ _

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

theorem USize64.le_iff_toNat_le {a b : USize64} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

theorem USize64.lt_iff_toNat_lt {a b : USize64} : a < b ↔ a.toNat < b.toNat := .rfl

theorem USize64.lt_ofNat_iff {n : USize64} {m : Nat} (h : m < size) :
  n < ofNat m ↔ n.toNat < m := UInt64.lt_ofNat_iff h

theorem USize64.ofNat_lt_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat :=
  UInt64.ofNat_lt_iff h

theorem USize64.le_ofNat_iff {n : USize64} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m :=
  UInt64.le_ofNat_iff h

theorem USize64.ofNat_le_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat :=
  UInt64.ofNat_le_iff h

@[grind]
theorem USize64.toNat_ofNat_of_lt' {n : Nat} (h : n < size) : (ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

@[grind]
theorem USize64.toNat_ofNat_of_lt {n : Nat} (h : n < size) : toNat (OfNat.ofNat n) = n :=
  UInt64.toNat_ofNat_of_lt h

additional_uint_decls USize64 64

namespace USize64

@[int_toBitVec] theorem le_iff_toBitVec_le {a b : USize64} : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl

@[int_toBitVec] theorem lt_iff_toBitVec_lt {a b : USize64} : a < b ↔ a.toBitVec < b.toBitVec := .rfl

@[simp] protected theorem toNat_zero : (0 : USize64).toNat = 0 := Nat.zero_mod _

@[simp, grind] protected theorem toNat_add (a b : USize64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add ..

protected theorem toNat_sub (a b : USize64) : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := BitVec.toNat_sub  ..

@[simp] protected theorem toNat_mul (a b : USize64) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul  ..

@[simp] protected theorem toNat_mod (a b : USize64) : (a % b).toNat = a.toNat % b.toNat := BitVec.toNat_umod ..

@[simp] protected theorem toNat_div (a b : USize64) : (a / b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv  ..

@[simp] protected theorem toNat_sub_of_le (a b : USize64) : b ≤ a → (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le

protected theorem toNat_lt_size (a : USize64) : a.toNat < size := a.toBitVec.isLt

protected theorem toNat.inj : ∀ {a b : USize64}, a.toNat = b.toNat → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected theorem toNat_inj : ∀ {a b : USize64}, a.toNat = b.toNat ↔ a = b :=
  Iff.intro toNat.inj (congrArg toNat)

end USize64

@[simp] theorem USize64.toNat_lt (n : USize64) : n.toNat < 2 ^ 64 := n.toFin.isLt

/-!
## Grind's ToInt

For grind to use integer arithmetic on `USize64`, we need the following instances, inspired by
the modules `Init.GrindInstances.ToInt` and `Init.GrindInstances.Ring.UInt`.
-/

namespace Lean.Grind

instance : ToInt USize64 (.uint 64) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := USize64.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (USize64.toNat_lt x)

@[simp] theorem toInt_usize64 (x : USize64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero USize64 (.uint 64) where
  toInt_zero := by simp

instance : ToInt.OfNat USize64 (.uint 64) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add USize64 (.uint 64) where
  toInt_add x y := by simp

instance : ToInt.Mul USize64 (.uint 64) where
  toInt_mul x y := by simp

instance : ToInt.Pow USize64 (.uint 64) := by sorry

instance : ToInt.Mod USize64 (.uint 64) where
  toInt_mod x y := by simp

instance : ToInt.Div USize64 (.uint 64) where
  toInt_div x y := by simp

instance : ToInt.LE USize64 (.uint 64) where
  le_iff x y := by simpa using USize64.le_iff_toBitVec_le

instance : ToInt.LT USize64 (.uint 64) where
  lt_iff x y := by simpa using USize64.lt_iff_toBitVec_lt


@[expose]
def USize64.natCast : NatCast USize64 where
  natCast x := USize64.ofNat x

@[expose]
def USize64.intCast : IntCast USize64 where
  intCast x := USize64.ofInt x

attribute [local instance] USize64.natCast USize64.intCast in
instance : CommRing USize64 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := sorry -- UInt64.add_assoc
  add_comm := sorry -- UInt64.add_comm
  add_zero := sorry -- UInt64.add_zero
  neg_add_cancel := sorry -- UInt64.add_left_neg
  mul_assoc := sorry -- UInt64.mul_assoc
  mul_comm := sorry -- UInt64.mul_comm
  mul_one := sorry -- UInt64.mul_one
  one_mul := sorry -- UInt64.one_mul
  left_distrib _ _ _ := sorry -- UInt64.mul_add
  right_distrib _ _ _ := sorry -- UInt64.add_mul
  zero_mul _ := sorry -- UInt64.zero_mul
  mul_zero _ := sorry -- UInt64.mul_zero
  sub_eq_add_neg := sorry -- UInt64.sub_eq_add_neg
  pow_zero := sorry -- UInt64.pow_zero
  pow_succ := sorry -- UInt64.pow_succ
  ofNat_succ x := sorry -- UInt64.ofNat_add x 1
  intCast_neg := sorry -- UInt64.ofInt_neg
  intCast_ofNat := sorry -- UInt64.intCast_ofNat
  neg_zsmul i a := by
    -- change (-i : Int) * a = - (i * a)
    sorry -- simp [UInt64.intCast_neg, UInt64.neg_mul]
  zsmul_natCast_eq_nsmul n a := sorry -- congrArg (· * a) (USize64.intCast_ofNat _)

instance : IsCharP USize64 18446744073709551616 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = USize64.ofNat x := rfl
    sorry -- simp [this, USize64.ofNat_eq_iff_mod_eq_toNat]
    )

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add USize64 (.uint 64) := inferInstance
example : ToInt.Neg USize64 (.uint 64) := {
  toInt_neg := sorry
}
example : ToInt.Sub USize64 (.uint 64) := {
  toInt_sub := sorry
}

end Lean.Grind


/-!
## Simp-Procs

Grind and simp use some simplification procedures for UInts. They are defined in
`Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt` and replicated here.
-/

namespace USize64
open Lean Meta Simp

instance : ToExpr USize64 where
  toTypeExpr := mkConst ``USize64
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``USize64) r
      (.app (.const ``USize64.instOfNat []) r)

def fromExpr (e : Expr) : SimpM (Option USize64) := do
  let some (n, _) ← getOfNatValue? e `USize64 | return none
  return USize64.ofNat n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : USize64 → USize64 → USize64) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : USize64 → USize64 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : USize64 → USize64 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceAdd ((_ + _ : USize64)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : USize64)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : USize64)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : USize64)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : USize64)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : USize64) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : USize64) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : USize64) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : USize64) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : USize64) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : USize64) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : USize64) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : USize64) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfNatLT (USize64.ofNatLT _ _) := fun e => do
  unless e.isAppOfArity `USize64.ofNatLT 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := USize64.ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (USize64.ofNat _) := fun e => do
  unless e.isAppOfArity `USize64.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := USize64.ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToNat (USize64.toNat _) := fun e => do
  unless e.isAppOfArity `USize64.toNat 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := USize64.toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : USize64)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end USize64
