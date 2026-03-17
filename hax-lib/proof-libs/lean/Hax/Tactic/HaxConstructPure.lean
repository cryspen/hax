import Hax.Tactic.HaxZify
import Hax.Tactic.HaxMvcgen
import Hax.MissingLean.Std.Do.Triple.PurifyLemmas
import Qq

open Lean Elab Tactic Meta Qq Std.Do

/-- Check whether a goal contains the given metavariable. -/
def goalContainsMVar (mvarId : MVarId) (goal : MVarId) : MetaM Bool := do
  let goalType ← instantiateMVars (← goal.getType)
  pure ((goalType.findMVar? (· == mvarId)).isSome)

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

  let allGoals ← getGoals
  -- Find goals containing the crucial metavariable
  let goals ← allGoals.filterM (fun g => liftM (goalContainsMVar crucialMVar g))

  -- If no goal contains the mvar, we're done (it was assigned)
  if goals.isEmpty then
    trace `Hax.hax_construct_pure fun () =>
      m!"haxPurifyStep: mvar {mkMVar crucialMVar} appears in none of the goals: {allGoals}"
    return

  if goals.length > 1 then
    throwError m!"hax_construct_pure: multiple goals contain the crucial metavariable. \
      This should not happen during purification."

  let [goal] := goals | return

  -- Introduce any binders in the goal before processing
  let (_, goal) ← goal.intros

  let env ← getEnv
  goal.withContext do
    let goalType ← goal.getType
    trace `Hax.hax_construct_pure fun () => m!"haxPurifyStep: goal = {goalType}"

    -- TODO: Layer 1 — meta-level match handling (Step 4 of the plan)

    -- Layer 2 — try @[purify] lemmas (single step only; recursion outside try/catch)
    let purifyDecls := purifyExt.getState env
    for declName in purifyDecls do
      let saved ← saveState
      try
        -- Need withAssignableSyntheticOpaque because the crucial mvar is synthetic opaque,
        -- and the purify lemma's conclusion must unify with the postcondition containing it.
        -- E.g., `r = ?p` must unify with `r = if c then ?pa else ?pb`.
        let newGoals ← withAssignableSyntheticOpaque do
          goal.apply (← mkConstWithFreshMVarLevels declName)
        let otherGoals := allGoals.filter (· != goal)
        setGoals (newGoals ++ otherGoals)
        trace `Hax.hax_construct_pure fun () =>
          m!"haxPurifyStep: applied @[purify] lemma `{declName}`, new goals: {newGoals}"
      catch _ =>
        saved.restore
        continue
      -- Purify lemma succeeded — the crucial mvar has been assigned (e.g., ?p := if c then ?pa else ?pb).
      -- Find the new crucial mvars from the assigned expression and recurse on each.
      let assignedExpr ← instantiateMVars (mkMVar crucialMVar)
      let newCrucialMVars := (assignedExpr.collectMVars {}).result
      for newMVar in newCrucialMVars do
        haxPurifyStep newMVar (fuel - 1)
      return

    -- Layer 3 — mvcgen fallback: one step of straight-line code
    do
      let saved ← saveState
      try
        let otherGoals := allGoals.filter (· != goal)
        setGoals (goal :: otherGoals)
        evalTactic (← `(tactic| mvcgen -leave -trivial (stepLimit := some 1)))
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
  let mvarVal : Q($type) ← mkFreshExprSyntheticOpaqueMVar type
  replaceMainGoal (← goal.apply q(@Subtype.mk $type $mvarP $mvarVal))
  -- Recursively purify the program
  haxPurifyStep mvarVal.mvarId!
