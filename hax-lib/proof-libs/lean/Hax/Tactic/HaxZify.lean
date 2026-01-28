import Lean
import Hax.Core_models

open Lean Elab Tactic Meta

/-- List of types supported by `hax_zify` -/
def haxZifyTypes := [
  (``Int8, ``Int8.toInt, ``Int8.ofInt_eq_of_toInt_eq),
  (``Int16, ``Int16.toInt, ``Int16.ofInt_eq_of_toInt_eq),
  (``Int32, ``Int32.toInt, ``Int32.ofInt_eq_of_toInt_eq),
  (``Int64, ``Int64.toInt, ``Int64.ofInt_eq_of_toInt_eq),
  (``UInt8, ``UInt8.toNat, ``UInt8.ofNat_eq_of_toNat_eq),
  (``UInt16, ``UInt16.toNat, ``UInt16.ofNat_eq_of_toNat_eq),
  (``UInt64, ``UInt64.toNat, ``UInt64.ofNat_eq_of_toNat_eq),
  (``USize64, ``USize64.toNat, ``USize64.ofNat_eq_of_toNat_eq),
]

/--
Replaces a variable of machine integer type by a variable of integer type. This roughly corresponds
to the application of the following tactics:
```
generalize h : var.toInt = x at *
replace h := Int32.ofInt_eq_of_toInt_eq h
subst h
```
-/
def haxZifySingle (mvarId : MVarId) (var : FVarId) (toInt ofInt_eq_of_toInt_eq : Name) : MetaM MVarId:= do
  mvarId.withContext do
    -- Generalize:
    let arg := {expr := ← mkAppM toInt #[mkFVar var], hName? := `h}
    let (_, newVars, mvarId) ← mvarId.generalizeHyp #[arg] ((← getLocalHyps).map (·.fvarId!))
    mvarId.withContext do
      unless newVars.size == 2 do
        Lean.Meta.throwTacticEx `hax_zify mvarId (m!"expected two variables, got {newVars.size}")
      -- Replace:
      let {mvarId, fvarId, ..} ← mvarId.replace newVars[1]! (← mkAppM ofInt_eq_of_toInt_eq #[mkFVar newVars[1]!])
      -- Subst:
      let (_, mvarId) ← substCore mvarId fvarId (symm := true)
      pure mvarId

/-- Replaces all variables of machine integer type by variables of integer type. -/
def haxZify (mvarId : MVarId) (declFilter : LocalDecl → Bool := fun _ => true) : MetaM MVarId := do
  mvarId.withContext do
    let mut mvarId := mvarId
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if !declFilter decl then continue
      let some (_, toInt, ofInt_eq_of_toInt_eq) ←
          haxZifyTypes.findM? fun (ty, _, _) => (isDefEq decl.type (mkConst ty))
        | continue
      let var := decl.fvarId
      mvarId ← haxZifySingle mvarId var toInt ofInt_eq_of_toInt_eq
    pure mvarId

/-- Replaces all variables of machine integer type in the current goal by variables of integer type. -/
elab "hax_zify" : tactic =>
  withMainContext do
    replaceMainGoal [(← haxZify (← getMainGoal))]
