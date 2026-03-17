import Hax.Tactic.HaxZify
import Hax.Tactic.HaxMvcgen
import Hax.MissingLean.Std.Do.Triple.PurifyLemmas
import Qq

open Lean Elab Tactic Meta Qq Std.Do

/-- Check whether a goal contains the given metavariable. -/
def goalContainsMVar (mvarId : MVarId) (goal : MVarId) : MetaM Bool := do
  let goalType ← instantiateMVars (← goal.getType)
  pure ((goalType.findMVar? (· == mvarId)).isSome)

/-- Find the unique goal containing `mvarId`. If no goal contains it and the mvar is still
unassigned, assign it to a default value (`Inhabited.default`). Returns `none` when done
(mvar was assigned or defaulted), or `some goal` when exactly one goal was found. -/
def findGoalForMVar (mvarId : MVarId) : TacticM (Option MVarId) := do
  let allGoals ← getGoals
  let goals ← allGoals.filterM (fun g => liftM (goalContainsMVar mvarId g))
  if goals.isEmpty then
    -- No goal contains the mvar — it was either assigned or only appears in side conditions.
    -- If still unassigned, assign it to a default value.
    unless ← mvarId.isAssignedOrDelayedAssigned do
      let (_, mvarId) ← mvarId.intros
      let mvarType ← mvarId.getType
      trace `Hax.hax_construct_pure fun () =>
        m!"findGoalForMVar: mvar {mkMVar mvarId} unassigned, assigning default of type {mvarType}"
      let defaultVal ← mkDefault mvarType
      mvarId.assign defaultVal
    return none
  if goals.length > 1 then
    throwError m!"hax_construct_pure: multiple goals contain the crucial metavariable. \
      This should not happen during purification: {goals}"
  let [goal] := goals | return none
  return some goal

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
  let some goal ← findGoalForMVar mvarId | return

  -- Introduce any binders in the goal before processing
  let (_, goal) ← goal.intros

  goal.withContext do
    -- Zify:
    let zifyVars ← collectZifyVars
    let goal ← haxZify goal (fun decl => zifyVars.contains decl.fvarId)
    trace `Hax.hax_construct_pure fun () => m!"Goal after `zify`: {goal}"
    -- Subst:
    let goal ← substVars goal
    trace `Hax.hax_construct_pure fun () => m!"Goal after `subst`: {goal}"
    -- Assign the meta-variable by reflexivity
    goal.applyRfl
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

/-- Recursively purify the program in the current goal. Steps through the program using:

1. **Match check:** If the program head is a `match`, handle at the meta-level by splitting
   the metavariable.
2. **`@[purify]` lemmas:** Try each registered purification lemma via `apply`. These handle
   control flow (ite, dite, loops).
3. **`mvcgen` fallback:** Use `mvcgen -leave -trivial` with stepLimit 1 to handle one step
   of straight-line code (unfolds, pure, bind).
-/
partial def haxPurifyStep (crucialMVar : MVarId) (fuel : Nat := 100) : TacticM Unit := do
  if fuel == 0 then
    throwError "hax_construct_pure: purification fuel exhausted"

  let some goal ← findGoalForMVar crucialMVar | return
  let allGoals ← getGoals

  -- Introduce any binders in the goal before processing
  let (_, goal) ← goal.intros

  let env ← getEnv
  goal.withContext do
    let goalType ← goal.getType
    trace `Hax.hax_construct_pure fun () => m!"haxPurifyStep: goal = {goalType}"

    -- TODO: Layer 1 — meta-level match handling (Step 4 of the plan)

    -- Layer 2 — try @[purify] lemmas via `mspec_no_bind`
    let purifyDecls := purifyExt.getState env
    for declName in purifyDecls do
      let saved ← saveState
      try
        let otherGoals := allGoals.filter (· != goal)
        setGoals (goal :: otherGoals)
        let declNameSyntax ← `($(mkIdent declName))
        evalTactic (← `(tactic| mspec_no_bind $declNameSyntax))
        pruneSolvedGoals
        trace `Hax.hax_construct_pure fun () =>
          m!"haxPurifyStep: applied @[purify] lemma `{declName}` via mspec"
      catch e =>
        let msg ← e.toMessageData.toString
        trace `Hax.hax_construct_pure fun () =>
          m!"haxPurifyStep: @[purify] lemma `{declName}` failed: {msg}"
        saved.restore
        continue
      -- Purify lemma succeeded. Find all Triple/SPred.entails goals produced by mspec
      -- and recurse on each, isolating the goal so the recursive call sees only it.
      let currentGoals ← getGoals
      let tripleGoals ← currentGoals.filterM fun g => do
        let ty ← instantiateMVars (← g.getType)
        let body := ty.getForallBody
        return body.isAppOf ``Std.Do.Triple || body.isAppOf ``Std.Do.SPred.entails
          || body.isAppOf ``Std.Tactic.Do.MGoalEntails
      trace `Hax.hax_construct_pure fun () =>
        m!"triple Goals: {tripleGoals}"
      let mut otherGoals := currentGoals.filter (fun g => !tripleGoals.contains g)
      trace `Hax.hax_construct_pure fun () =>
        m!"other Goals: {otherGoals}"
      for tripleGoal in tripleGoals do
        let ty ← instantiateMVars (← tripleGoal.getType)
        let goalMVars := (ty.collectMVars {}).result
        setGoals [tripleGoal]
        for mvarId in goalMVars do
          haxPurifyStep mvarId (fuel - 1)
        otherGoals := otherGoals ++ (← getGoals)
      setGoals otherGoals
      pruneSolvedGoals
      return

    -- Layer 3 — mvcgen fallback: one step of straight-line code
    do
      let saved ← saveState
      try
        let otherGoals := allGoals.filter (· != goal)
        setGoals (goal :: otherGoals)
        evalTactic (← `(tactic| hax_mvcgen -leave -trivial (stepLimit := some 1)))
        let newGoals ← getGoals
        -- Check that mvcgen actually made progress (goal types changed)
        let newGoalTypes ← newGoals.mapM (·.getType)
        let oldGoalTypes ← allGoals.mapM (·.getType)
        if newGoalTypes == oldGoalTypes then
          throwError "no progress"
        trace `Hax.hax_construct_pure fun () =>
          m!"haxPurifyStep: after mvcgen step, goals: {newGoals}"
      catch _ =>
        saved.restore
        -- Layer 4 — leave stateful proof mode, then instantiate the metavariable via zify + subst + rfl
        trace `Hax.hax_construct_pure fun () =>
          m!"haxPurifyStep: try to instantiate the metavariable"
        let otherGoals := allGoals.filter (· != goal)
        setGoals (goal :: otherGoals)
        evalTactic (← `(tactic| mleave))
        haxConstructPure crucialMVar
        return
      -- mvcgen step succeeded — recurse outside try/catch
      haxPurifyStep crucialMVar (fuel - 1)

/-- The `hax_construct_pure` tactic should be applied to goals of the form
```
 { p // ⦃⌜ ... ⌝⦄ ... ⦃⇓ r => ⌜r = p⌝⦄ }
```
Under the hood, it will step through the program using `@[purify]` lemmas and `mvcgen` to
recursively purify the program and generate a suitable value for `p`.
 -/
syntax (name := hax_construct_pure) "hax_construct_pure" : tactic

@[tactic hax_construct_pure]
def elabHaxConstructPure : Tactic := fun _stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  unless goalType.isAppOf ``Subtype do
    throwError m!"hax_construct_pure: Goal must be of the form `\{ p // ... }` (Subtype), \
      but got:\n{goalType}"

  let u ← mkFreshLevelMVar
  let type : Q(Type) ← mkFreshExprMVar (mkSort u) MetavarKind.natural Name.anonymous
  let mvarP : Q($type → Prop) ← mkFreshExprMVar q($type → Prop)
  let mvarVal : Q($type) ← mkFreshExprMVar type MetavarKind.natural
  replaceMainGoal (← goal.apply q(@Subtype.mk $type $mvarP $mvarVal))
  -- Recursively purify the program
  haxPurifyStep mvarVal.mvarId!
