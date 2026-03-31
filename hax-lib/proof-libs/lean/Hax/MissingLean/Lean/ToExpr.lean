import Lean
import Hax.MissingLean.Init.Data.UInt.Basic
import Hax.MissingLean.Init.Data.SInt.Basic_Int128

open Lean in
instance : ToExpr UInt128 where
  toTypeExpr := mkConst ``UInt128
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``UInt128) r
      (.app (.const ``UInt128.instOfNat []) r)

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
