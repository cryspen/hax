import Lean
import Hax.MissingLean.Lean.ToExpr

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

simproc [simp, seval] reduceLT  (( _ : UInt128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : UInt128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : UInt128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : UInt128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : UInt128) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : UInt128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
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
