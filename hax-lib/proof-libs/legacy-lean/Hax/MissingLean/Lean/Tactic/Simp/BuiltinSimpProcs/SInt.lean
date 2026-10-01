import Lean
import Hax.MissingLean.Lean.ToExpr


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

simproc [simp, seval] reduceLT  (( _ : Int128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : Int128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : Int128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : Int128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : Int128) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : Int128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
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
