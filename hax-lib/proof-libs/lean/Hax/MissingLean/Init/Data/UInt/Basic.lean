import Hax.MissingLean.Init.Data.UInt.BasicAux

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

open Lean in
set_option hygiene false in
macro "additional_uint_decls" typeName:ident width:term : command => do
  let mut cmds := ← Syntax.getArgs <$> `(
    namespace $typeName

    theorem toNat_add_of_lt {x y : $typeName} (h : x.toNat + y.toNat < 2 ^ $width) :
        (x + y).toNat = x.toNat + y.toNat := BitVec.toNat_add_of_lt h

    theorem toNat_sub_of_le' {x y : $typeName} (h : y.toNat ≤ x.toNat) :
        (x - y).toNat = x.toNat - y.toNat := BitVec.toNat_sub_of_le h

    theorem toNat_mul_of_lt {x y : $typeName} (h : x.toNat * y.toNat < 2 ^ $width) :
        (x * y).toNat = x.toNat * y.toNat := BitVec.toNat_mul_of_lt h

    def addOverflow (a b : $typeName) : Bool :=
      BitVec.uaddOverflow a.toBitVec b.toBitVec

    def subOverflow (a b : $typeName) : Bool :=
      BitVec.usubOverflow a.toBitVec b.toBitVec

    def mulOverflow (a b : $typeName) : Bool :=
      BitVec.umulOverflow a.toBitVec b.toBitVec

    @[grind .]
    theorem addOverflow_iff {a b : $typeName} : addOverflow a b ↔ a.toNat + b.toNat ≥ 2 ^ $width :=
      decide_eq_true_iff

    @[grind .]
    theorem subOverflow_iff {a b : $typeName} : subOverflow a b ↔ a.toNat < b.toNat :=
      decide_eq_true_iff

    @[grind .]
    theorem mulOverflow_iff {a b : $typeName} : mulOverflow a b ↔ a.toNat * b.toNat ≥ 2 ^ $width :=
      decide_eq_true_iff

    end $typeName
  )
  return ⟨mkNullNode cmds⟩

additional_uint_decls UInt8 8
additional_uint_decls UInt16 16
additional_uint_decls UInt32 32
additional_uint_decls UInt64 64
additional_uint_decls UInt128 128
additional_uint_decls USize System.Platform.numBits

open Lean in
set_option hygiene false in
macro "declare_missing_uint_conversions" : command => do
  let mut cmds := #[]
  let src : List (Name × Nat) := [
    (`UInt8, 8),
    (`UInt16, 16),
    (`UInt32, 32),
    (`UInt64, 64),
    (`USize, 0),
  ]
  let dst : List (Name × Nat) := [
    (`Int8, 8),
    (`Int16, 16),
    (`Int32, 32),
    (`Int64, 64),
    (`ISize, 0)
  ]
  for (srcName, srcIdx) in src do
    for (dstName, dstIdx) in dst do
      let srcIdent := mkIdent srcName
      let dstIdent := mkIdent dstName
      if srcIdx != dstIdx then
        cmds := cmds.push $ ← `(
          def $(mkIdent (srcName ++ dstName.appendBefore "to")) (x : $srcIdent) : $dstIdent :=
            $(mkIdent (`Nat ++ dstName.appendBefore "to")) x.toNat
        )
  return ⟨mkNullNode cmds⟩

declare_missing_uint_conversions
