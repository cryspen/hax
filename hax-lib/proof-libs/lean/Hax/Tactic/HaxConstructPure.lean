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
def findUniqueGoalForMVar (mvarId : MVarId) : TacticM (Option MVarId) := do
  let currentGoals ← getGoals
  let goals ← currentGoals.filterM (fun g => liftM (goalContainsMVar mvarId g))
  if goals.isEmpty then
    -- No goal contains the mvar — it was either assigned or only appears in side conditions.
    -- If still unassigned, assign it to a default value.
    unless ← mvarId.isAssignedOrDelayedAssigned do
      let (_, mvarId) ← mvarId.intros
      let mvarType ← mvarId.getType
      trace `Hax.hax_construct_pure fun () =>
        m!"findUniqueGoalForMVar: mvar {mkMVar mvarId} unassigned, assigning default of type {mvarType}"
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
def finalizePureMVar (pureMVar : MVarId) : TacticM Unit := do
  let some goal ← findUniqueGoalForMVar pureMVar | return

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
partial def purifyStep (pureMVar : MVarId) (fuel : Nat := 100) : TacticM Unit := do
  if fuel == 0 then
    throwError "hax_construct_pure: purification fuel exhausted"

  let some goal ← findUniqueGoalForMVar pureMVar | return

  -- Introduce any binders in the goal before processing
  let (_, goal) ← goal.intros
  let currentGoals ← getGoals

  let env ← getEnv
  goal.withContext do
    let goalType ← goal.getType
    trace `Hax.hax_construct_pure fun () => m!"purifyStep: goal = {goalType}"

    -- TODO: Layer 1 — meta-level match handling (Step 4 of the plan)

    -- Layer 2 — try @[purify] lemmas via `mspec_no_bind`
    let purifyDecls := purifyExt.getState env
    for declName in purifyDecls do
      let saved ← saveState
      try
        let sideGoals := currentGoals.filter (· != goal)
        setGoals (goal :: sideGoals)
        let declNameSyntax ← `($(mkIdent declName))
        evalTactic (← `(tactic| mspec_no_bind $declNameSyntax))
        pruneSolvedGoals
        trace `Hax.hax_construct_pure fun () =>
          m!"purifyStep: applied @[purify] lemma `{declName}` via mspec"
      catch e =>
        let msg ← e.toMessageData.toString
        trace `Hax.hax_construct_pure fun () =>
          m!"purifyStep: @[purify] lemma `{declName}` failed: {msg}"
        saved.restore
        continue
      -- Purify lemma succeeded. Find all Triple/SPred.entails goals produced by mspec
      -- and recurse on each, isolating the goal so the recursive call sees only it.
      let postMspecGoals ← getGoals
      let recurGoals ← postMspecGoals.filterM fun g => do
        let ty ← instantiateMVars (← g.getType)
        let body := ty.getForallBody
        return body.isAppOf ``Std.Do.Triple || body.isAppOf ``Std.Do.SPred.entails
          || body.isAppOf ``Std.Tactic.Do.MGoalEntails
      trace `Hax.hax_construct_pure fun () =>
        m!"recurGoals: {recurGoals}"
      let mut sideGoals := postMspecGoals.filter (fun g => !recurGoals.contains g)
      trace `Hax.hax_construct_pure fun () =>
        m!"sideGoals: {sideGoals}"
      for recurGoal in recurGoals do
        let ty ← instantiateMVars (← recurGoal.getType)
        -- Extract the postcondition (last argument of Triple/SPred.entails/MGoalEntails)
        let postcond := ty.getForallBody.getAppArgs.back!
        let postcondMVars := (postcond.collectMVars {}).result
        -- Only recurse on natural mvars (the "pure value" mvars), skip synthetic/type mvars
        let pureMVars ← postcondMVars.filterM fun mv => do
          let decl ← mv.getDecl
          return decl.kind matches .natural
        if pureMVars.size != 1 then
          throwError m!"hax_construct_pure: expected exactly one natural mvar in postcondition, \
            but found {pureMVars.size}: {pureMVars.map mkMVar}"
        setGoals [recurGoal]
        for mvarId in pureMVars do
          purifyStep mvarId (fuel - 1)
        sideGoals := sideGoals ++ (← getGoals)
      setGoals sideGoals
      pruneSolvedGoals
      return

    -- Layer 3 — mvcgen fallback: one step of straight-line code
    do
      let saved ← saveState
      try
        let sideGoals := currentGoals.filter (· != goal)
        setGoals (goal :: sideGoals)
        evalTactic (← `(tactic| hax_mvcgen -leave -trivial (stepLimit := some 1)))
        let newGoals ← getGoals
        -- Check that mvcgen actually made progress (goal types changed)
        let newGoalTypes ← newGoals.mapM (·.getType)
        let oldGoalTypes ← currentGoals.mapM (·.getType)
        if newGoalTypes.length == oldGoalTypes.length &&
            (newGoalTypes.zip oldGoalTypes).all fun (a, b) => a.equal b then
          throwError "no progress"
        trace `Hax.hax_construct_pure fun () =>
          m!"purifyStep: after mvcgen step, goals: {newGoals}"
      catch _ =>
        saved.restore
        -- Layer 4 — leave stateful proof mode, then instantiate the metavariable via zify + subst + rfl
        trace `Hax.hax_construct_pure fun () =>
          m!"purifyStep: try to instantiate the metavariable"
        let sideGoals := currentGoals.filter (· != goal)
        setGoals (goal :: sideGoals)
        evalTactic (← `(tactic| mleave))
        finalizePureMVar pureMVar
        return
      -- mvcgen step succeeded — check that the mvar wasn't duplicated across goals, then recurse
      let postMvcgenGoals ← getGoals
      let mvarGoals ← postMvcgenGoals.filterM (fun g => liftM (goalContainsMVar pureMVar g))
      if mvarGoals.length > 1 then
        throwError m!"hax_construct_pure: mvcgen split the pure mvar across multiple goals. \
          Previous goal was:\n{goalType}"
      purifyStep pureMVar (fuel - 1)

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
  purifyStep mvarVal.mvarId!
