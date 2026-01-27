/-
Hax Lean Backend - Cryspen

Support for integer operations
-/

import Hax.Lib
import Hax.CoreModels
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


/-

# Arithmetic operations

The Rust arithmetic operations have their own notations, using a `?`. They
return a `RustM`, that is `.fail` when arithmetic overflows occur.

-/

infixl:65 " +? "   => @Core_models.Ops.Arith.Add.add _ _
infixl:65 " -? "   => @Core_models.Ops.Arith.Sub.sub _ _
infixl:70 " *? "   => @Core_models.Ops.Arith.Mul.mul _ _
infixl:75 " >>>? " => @Core_models.Ops.Bit.Shr.shr _ _
infixl:75 " <<<? " => @Core_models.Ops.Bit.Shl.shl _ _
infixl:70 " %? "   => @Core_models.Ops.Arith.Rem.rem _ _
infixl:70 " /? "   => @Core_models.Ops.Arith.Div.div _ _
prefix:75 "-?"   => @Core_models.Ops.Arith.Neg.neg _

attribute [hax_bv_decide]
  Core_models.Ops.Arith.Add.AssociatedTypes.Output
  Core_models.Ops.Arith.Sub.AssociatedTypes.Output
  Core_models.Ops.Arith.Mul.AssociatedTypes.Output
  Core_models.Ops.Arith.Div.AssociatedTypes.Output
  Core_models.Ops.Arith.Rem.AssociatedTypes.Output
  Core_models.Ops.Arith.Neg.AssociatedTypes.Output
  Core_models.Ops.Bit.Shl.AssociatedTypes.Output
  Core_models.Ops.Bit.Shr.AssociatedTypes.Output
  Core_models.Ops.Arith.Add.add
  Core_models.Ops.Arith.Sub.sub
  Core_models.Ops.Arith.Mul.mul
  Core_models.Ops.Bit.Shr.shr
  Core_models.Ops.Bit.Shl.shl
  Core_models.Ops.Arith.Rem.rem
  Core_models.Ops.Arith.Div.div
  Core_models.Ops.Arith.Neg.neg

open Lean in
macro "declare_Hax_int_ops" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do

  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax

  let mut cmds ← Syntax.getArgs <$> `(

    @[reducible] instance : Core_models.Ops.Arith.Add.AssociatedTypes $typeName $typeName where
      Output := $typeName
    @[reducible] instance : Core_models.Ops.Arith.Sub.AssociatedTypes $typeName $typeName where
      Output := $typeName
    @[reducible] instance : Core_models.Ops.Arith.Mul.AssociatedTypes $typeName $typeName where
      Output := $typeName
    @[reducible] instance : Core_models.Ops.Arith.Div.AssociatedTypes $typeName $typeName where
      Output := $typeName
    @[reducible] instance : Core_models.Ops.Arith.Rem.AssociatedTypes $typeName $typeName where
      Output := $typeName
    @[reducible] instance : Core_models.Ops.Arith.Neg.AssociatedTypes $typeName where
      Output := $typeName

    /-- Addition on Rust integers. Panics on overflow. -/
    instance : Core_models.Ops.Arith.Add $typeName $typeName where
      add x y :=
        if ($(mkIdent (if signed then `BitVec.saddOverflow else `BitVec.uaddOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x + y)

    /-- Subtraction on Rust integers. Panics on overflow. -/
    instance : Core_models.Ops.Arith.Sub $typeName $typeName where
      sub x y :=
        if ($(mkIdent (if signed then `BitVec.ssubOverflow else `BitVec.usubOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x - y)

    /-- Multiplication on Rust integers. Panics on overflow. -/
    instance : Core_models.Ops.Arith.Mul $typeName $typeName where
      mul x y :=
        if ($(mkIdent (if signed then `BitVec.smulOverflow else `BitVec.umulOverflow)) x.toBitVec y.toBitVec) then
          .fail .integerOverflow
        else pure (x * y)
  )
  if signed then
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /-- Division of signed Rust integers. Panics on overflow (when x is IntMin and `y = -1`)
        and when dividing by zero. -/
      instance : Core_models.Ops.Arith.Div $typeName $typeName where
        div x y :=
          if x = $(mkIdent (typeName.getId ++ `minValue)) && y = -1 then .fail .integerOverflow
          else if y = 0 then .fail .divisionByZero
          else pure (x / y)

      /-- Remainder of signed Rust integers. Panics on overflow (when x is IntMin and `y = -1`)
        and when the modulus is zero. -/
      instance : Core_models.Ops.Arith.Rem $typeName $typeName where
        rem x y :=
          if x = $(mkIdent (typeName.getId ++ `minValue)) && y = -1 then .fail .integerOverflow
          else if y = 0 then .fail .divisionByZero
          else pure (x % y)

      instance : Core_models.Ops.Arith.Neg $typeName where neg := fun x => pure (- x)
    )
  else -- unsigned
    cmds := cmds.append $ ← Syntax.getArgs <$> `(
      /-- Division on unsigned Rust integers. Panics when dividing by zero.  -/
      instance : Core_models.Ops.Arith.Div $typeName $typeName where
        div x y :=
          if y = 0 then .fail .divisionByZero
          else pure (x / y)

      /-- Division on unsigned Rust integers. Panics when the modulus is zero. -/
      instance : Core_models.Ops.Arith.Rem $typeName $typeName where
        rem x y :=
          if y = 0 then .fail .divisionByZero
          else pure (x % y)
    )
  return ⟨mkNullNode cmds⟩

declare_Hax_int_ops unsigned UInt8 8
declare_Hax_int_ops unsigned UInt16 16
declare_Hax_int_ops unsigned UInt32 32
declare_Hax_int_ops unsigned UInt64 64
declare_Hax_int_ops unsigned USize64 64
declare_Hax_int_ops signed Int8 8
declare_Hax_int_ops signed Int16 16
declare_Hax_int_ops signed Int32 32
declare_Hax_int_ops signed Int64 64
declare_Hax_int_ops signed ISize System.Platform.numBits



open Lean in
set_option hygiene false in
macro "declare_Hax_shift_ops" : command => do
  let mut cmds := #[]
  let tys := [
    ("UInt8", ← `(term| 8)),
    ("UInt16", ← `(term| 16)),
    ("UInt32", ← `(term| 32)),
    ("UInt64", ← `(term| 64)),
    ("USize64", ← `(term| 64)),
    ("Int8", ← `(term| 8)),
    ("Int16", ← `(term| 16)),
    ("Int32", ← `(term| 32)),
    ("Int64", ← `(term| 64)),
    ("ISize", ← `(term| OfNat.ofNat System.Platform.numBits))
  ]
  for (ty1, width1) in tys do
    for (ty2, width2) in tys do

      let ty1Ident := mkIdent ty1.toName
      let ty2Ident := mkIdent ty2.toName
      let toTy1 := mkIdent ("to" ++ ty1).toName
      let ty2Signed := ty2.startsWith "I"
      let ty2ToNat := mkIdent (if ty2Signed then `toNatClampNeg else `toNat)
      let yConverted ← if ty1 == ty2 then `(y) else `(y.$ty2ToNat.$toTy1)

      cmds := cmds.push $ ← `(
        @[reducible]
        instance : Core_models.Ops.Bit.Shr.AssociatedTypes $ty1Ident $ty2Ident where
          Output := $ty1Ident
        @[reducible]
        instance : Core_models.Ops.Bit.Shl.AssociatedTypes $ty1Ident $ty2Ident where
          Output := $ty1Ident

        /-- Shift right for Rust integers. Panics when shifting by a negative number or
          by the bitsize or more. -/
        instance : Core_models.Ops.Bit.Shr $ty1Ident $ty2Ident where
          shr x y :=
            if 0 ≤ y && y < $width1
            then pure (x >>> $yConverted)
            else .fail .integerOverflow

        /-- Left shifting on signed integers. Panics when shifting by a negative number,
          or when shifting by more than the size. -/
        instance : Core_models.Ops.Bit.Shl $ty1Ident $ty2Ident where
          shl x y :=
            if 0 ≤ y && y < $width1
            then pure (x <<< $yConverted)
            else
              .fail .integerOverflow
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_shift_ops


open Lean in
set_option hygiene false in
macro "declare_Hax_convert_from_instances" : command => do
  let mut cmds := #[]
  let tys := [
    ("UInt8", 8, false),
    ("UInt16", 16, false),
    ("UInt32", 32, false),
    ("UInt64", 64, false),
    ("Int8", 8, true),
    ("Int16", 16, true),
    ("Int32", 32, true),
    ("Int64", 64, true)
  ]
  for (ty1, width1, signed1) in tys do
    for (ty2, width2, signed2) in tys do

      if ty1 == ty2 || signed1 != signed2 || width1 < width2 then continue

      let ty1Ident := mkIdent ty1.toName
      let ty2Ident := mkIdent ty2.toName
      let toTy1 := mkIdent ("to" ++ ty1).toName

      cmds := cmds.push $ ← `(
        @[reducible]
        instance : Core_models.Convert.From.AssociatedTypes $ty1Ident $ty2Ident where
        instance : Core_models.Convert.From $ty1Ident $ty2Ident where
          _from := fun x => x.$toTy1
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_convert_from_instances

attribute [hax_bv_decide]
  Core_models.Convert.From._from
