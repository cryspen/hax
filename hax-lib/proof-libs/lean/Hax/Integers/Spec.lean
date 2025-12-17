/-
Hax Lean Backend - Cryspen

Specifications for integer operations
-/

import Hax.Lib
import Hax.Integers.Ops
import Hax.MissingLean
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

attribute [spec]
  BitVec.uaddOverflow
  BitVec.usubOverflow
  BitVec.umulOverflow

open Lean in
macro "declare_Hax_int_ops_spec" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do

  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax

  let mut cmds ← Syntax.getArgs <$> `(
    namespace $typeName
      /-- Bitvec-based specification for rust addition -/
      @[spec]
      theorem haxAdd_spec (x y : $typeName):
        ¬ ($(mkIdent (if signed then `BitVec.saddOverflow else `BitVec.uaddOverflow)) x.toBitVec y.toBitVec) →
        ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓ r => ⌜ r = x + y ⌝ ⦄
        := by intros; mvcgen [HaxAdd.add]

      /-- Bitvec-based specification for rust subtraction -/
      @[spec]
      theorem haxSub_spec (x y : $typeName):
        ¬ ($(mkIdent (if signed then `BitVec.ssubOverflow else `BitVec.usubOverflow)) x.toBitVec y.toBitVec) →
        ⦃ ⌜ True ⌝ ⦄ (x -? y) ⦃ ⇓ r => ⌜ r = x - y ⌝ ⦄
        := by intros; mvcgen [HaxSub.sub]

      /-- Bitvec-based specification for rust multiplication -/
      @[spec]
      theorem haxMul_spec (x y : $typeName):
        ¬ ($(mkIdent (if signed then `BitVec.smulOverflow else `BitVec.umulOverflow)) x.toBitVec y.toBitVec) →
        ⦃ ⌜ True ⌝ ⦄ (x *? y) ⦃ ⇓ r => ⌜ r = x * y ⌝ ⦄
        := by intros; mvcgen [HaxMul.mul]
  )
  if signed then
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /-- Bitvec-based specification for rust multiplication for signed integers-/
      @[spec]
      theorem haxDiv_spec (x y : $typeName):
        ¬ y = 0 →
        ¬ (BitVec.sdivOverflow x.toBitVec y.toBitVec) →
        ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
        := by intros; mvcgen [HaxDiv.div]

      /-- Bitvec-based specification for rust remainder for signed integers -/
      @[spec]
      theorem haxRem_spec (x y : $typeName):
        ¬ y = 0 →
        ¬ (BitVec.sdivOverflow x.toBitVec y.toBitVec) →
        ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
        := by intros; mvcgen [HaxRem.rem]
    )
  else -- unsigned
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /-- Bitvec-based specification for rust multiplication for unsigned integers -/
      @[spec]
      theorem haxDiv_spec (x y : $typeName):
        ¬ y = 0 →
        ⦃ ⌜ True ⌝ ⦄ (x /? y) ⦃ ⇓ r => ⌜ r = x / y ⌝ ⦄
        := by intros; mvcgen [HaxDiv.div]

      /-- Bitvec-based specification for rust remainder for unsigned integers -/
      @[spec]
      theorem haxRem_spec (x y : $typeName):
        ¬ y = 0 →
        ⦃ ⌜ True ⌝ ⦄ (x %? y) ⦃ ⇓ r => ⌜ r = x % y ⌝ ⦄
        := by intros; mvcgen [HaxRem.rem]
    )
  cmds := cmds.push $ ← `(
    end $typeName
  )
  return ⟨mkNullNode cmds⟩

declare_Hax_int_ops_spec unsigned UInt8 8
declare_Hax_int_ops_spec unsigned UInt16 16
declare_Hax_int_ops_spec unsigned UInt32 32
declare_Hax_int_ops_spec unsigned UInt64 64
declare_Hax_int_ops_spec unsigned USize System.Platform.numBits
declare_Hax_int_ops_spec signed Int8 8
declare_Hax_int_ops_spec signed Int16 16
declare_Hax_int_ops_spec signed Int32 32
declare_Hax_int_ops_spec signed Int64 64
declare_Hax_int_ops_spec signed ISize System.Platform.numBits

open Lean in
macro "declare_Hax_shift_ops_spec" : command => do
  let mut cmds := #[]
  let tys := [
    ("UInt8", ← `(term| 8)),
    ("UInt16", ← `(term| 16)),
    ("UInt32", ← `(term| 32)),
    ("UInt64", ← `(term| 64)),
    ("Int8", ← `(term| 8)),
    ("Int16", ← `(term| 16)),
    ("Int32", ← `(term| 32)),
    ("Int64", ← `(term| 64)),
  ]
  for (ty1, width1) in tys do
    for (ty2, width2) in tys do

      let ty1Ident := mkIdent ty1.toName
      let ty2Ident := mkIdent ty2.toName
      let toTy1 := mkIdent ("to" ++ ty1).toName
      let ty2Signed := ty2.startsWith "I"
      let ty2ToNat := mkIdent (if ty2Signed then `toNatClampNeg else `toNat)
      let yConverted ← if ty1 == ty2 then `(y) else `(y.$ty2ToNat.$toTy1)
      let haxShiftRight_spec := mkIdent ("haxShiftRight_" ++ ty2 ++ "_spec").toName
      let haxShiftLeft_spec := mkIdent ("haxShiftLeft_" ++ ty2 ++ "_spec").toName

      cmds := cmds.push $ ← `(
        namespace $ty1Ident
          /-- Bitvec-based specification for rust remainder on unsigned integers -/
          @[spec]
          theorem $haxShiftRight_spec (x : $ty1Ident) (y : $ty2Ident) :
            0 ≤ y →
            y.$ty2ToNat < $width1 →
            ⦃ ⌜ True ⌝ ⦄ (x >>>? y) ⦃ ⇓ r => ⌜ r = x >>> $yConverted ⌝ ⦄
            := by intros; mvcgen [HaxShiftRight.shiftRight]; grind

          /-- Bitvec-based specification for rust remainder on unsigned integers -/
          @[spec]
          theorem $haxShiftLeft_spec (x : $ty1Ident) (y : $ty2Ident) :
            0 ≤ y →
            y.$ty2ToNat < $width1 →
            ⦃ ⌜ True ⌝ ⦄ (x <<<? y) ⦃ ⇓ r => ⌜ r = x <<< $yConverted ⌝ ⦄
            := by intros; mvcgen [HaxShiftLeft.shiftLeft]; grind
        end $ty1Ident
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_shift_ops_spec
