import Lean
import Qq
import Hax.Lib
import Hax.Integers.Spec

open Lean Elab Tactic Meta Qq Std.Do

macro "hax_bv_decide" c:Lean.Parser.Tactic.optConfig : tactic => `(tactic| (
  simp only [hax_bv_decide] at *; bv_decide $c
))

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

/-- This tactic is supposed to be run on results of `mvcgen` where the postcondition is of the form
`⇓ r => r = ?mvar`. This tactic will analyse the goals produced by `mvcgen` and instantiate the
metavariable accordingly.

For example, `mvcgen` might produce a goal of the form
```
x r : Int32
h : r.toInt = x.toInt + x.toInt
⊢ ((r.toInt == 0) = true) = ?mvar
```
Then this tactic should instantiate `?mvar` with `((x.toInt + x.toInt == 0) = true)`
-/
def haxConstructPure (mvarId : MVarId) : TacticM Unit := do
  -- Find goals that contain `mvar`
  let allGoals ← getGoals
  let goals ← allGoals.filterM
    fun goal => do pure ((← goal.getType).findMVar? (· == mvarId)).isSome
  if (goals.length > 1) then
    throwError m!"hax_construct_pure: `mvcgen generated more than one goal containing the \
      metavariable. This is currently unsupported. Try to remove if-then-else and match-constructs."
  let [goal] := goals
    | throwError m!"hax_construct_pure: No goal contains the metavariable."

  goal.withContext do
    -- Zify:
    let zifyVars ← collectZifyVars
    let goal ← haxZify goal (fun decl => zifyVars.contains decl.fvarId)
    trace `Hax.hax_construct_pure fun () => m!"Goal after `zify`: {goal}"
    -- Subst:
    let goal ← substVars goal
    trace `Hax.hax_construct_pure fun () => m!"Goal after `subst`: {goal}"
    -- Assign the meta-variable by reflexivity
    withAssignableSyntheticOpaque goal.applyRfl
    pruneSolvedGoals
where
  /-- Collect all machine integer variables that should be converted into integers. We want to
  collect all variables `x` with a hypothesis of the form `x.toInt = ...` here. Then,
  `hax_zify` will convert this into a hypothesis of the form `y = ...` for a new integer variable
  `y`, which we can ultimately eliminate using `subst_vars`. -/
  collectZifyVars : MetaM (Std.HashSet FVarId) := do
    let lctx ← getLCtx
    let mut zifyVars := Std.HashSet.emptyWithCapacity lctx.size
    for decl in lctx do
      if !decl.type.isEq then continue
      let lhs := decl.type.getArg! 1
      if !haxZifyTypes.any (fun (_, toInt, _) => lhs.isAppOfArity toInt 1) then continue
      let some fvarId := (lhs.getArg! 0).fvarId?
        | continue
      zifyVars := zifyVars.insert fvarId
    return zifyVars

/-- The `hax_construct_pure` tactic should be applied to goals of the form
```
 { p // ⦃⌜ ... ⌝⦄ ... ⦃⇓ r => ⌜r = p⌝⦄ }
```
Under the hood, it will use `mvcgen` to generate verification conditions for the given Hoare
triple and then generate a suitable value for `p`. The default call to `mvcgen` can be replaced
via the syntax `hax_construct_pure => custom_tactics`.
 -/
syntax (name := hax_construct_pure) "hax_construct_pure" (" => " tacticSeq)? : tactic

@[tactic hax_construct_pure]
def elabHaxConstructPure : Tactic := fun stx => do
  let tac ← match stx with
  | `(tactic| hax_construct_pure => $tac:tacticSeq) => pure tac
  | `(tactic| hax_construct_pure) => `(tacticSeq| mvcgen)
  | _ => throwUnsupportedSyntax

  let goal ← getMainGoal
  let goalType ← goal.getType

  unless goalType.isAppOf ``Subtype do
    throwError m!"hax_construct_pure: Goal must be of the form `\{ p // ... }` (Subtype), \
      but got:\n{goalType}"

  let u ← mkFreshLevelMVar
  let type : Q(Type) ← mkFreshExprMVar (mkSort u) MetavarKind.natural Name.anonymous
  let mvarP : Q($type → Prop) ← mkFreshExprMVar q($type → Prop)
  let mvarVal : Q($type) ← mkFreshExprSyntheticOpaqueMVar type
  replaceMainGoal (← goal.apply q(@Subtype.mk $type $mvarP $mvarVal))
  evalTactic (← `(tactic| intros))
  evalTactic tac
  let goals ← getGoals
  trace `Hax.hax_construct_pure fun () => m!"Goals after `mvcgen`: {goals}"
  haxConstructPure mvarVal.mvarId!

initialize registerTraceClass `Hax.hax_construct_pure
