import Lean
import Hax.core_models
import Hax.Tactic.HaxMvcgenAtGoal

set_option autoImplicit true

open Lean Std.Do Elab Parser Tactic Meta

theorem triple_in_hypothesis {f : RustM α} {Q : α → Assertion _} (p : Prop)
  (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
  (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
p := sorry

def haxMvcgenAt (mainGoal : MVarId) (hyp : LocalDecl) (cfgStx : TSyntax `Lean.Parser.Tactic.optConfig) (argStx : Syntax) : TacticM (List MVarId) := do
  forallTelescope (cleanupAnnotations := true) (← instantiateMVars hyp.type) fun xs hbody => do

    let hbody ← whnfR hbody
    unless hbody.isAppOfArity' ``Triple 7 do
      Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Expected `Std.Do.Triple`, got {hbody}")

    -- Create an MVar `newHyp` of type `Prop` representing the expression that `hyp` will be
    -- replaced with. We will determin what `newHyp` states later.
    let newHyp ← mkFreshExprMVar (kind := .syntheticOpaque) (mkSort .zero)

    -- To prove `newHyp`, we apply `triple_in_hypothesis`, followed by `hax_mvcgen`.
    let newHypProof ← mkFreshExprMVar newHyp
    let lemma ← mkAppM ``triple_in_hypothesis #[newHyp, mkAppN (mkFVar hyp.fvarId) xs]
    let goals ← newHypProof.mvarId!.apply lemma
    let [goal, _] := goals
      | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal
          (m!"Unexpected number of goals after `triple_in_hypothesis`: {goals}")
    let previousLctxSize ← goal.withContext do pure (← getLCtx).decls.size
    let cfgStx : TSyntax `Lean.Parser.Tactic.optConfig :=
      Parser.Tactic.appendConfig cfgStx (← `(Lean.Parser.Tactic.optConfig| -trivial))
    let inner : TSyntax `tactic := ⟨Syntax.node .none ``Hax.HaxMvcgen.hax_mvcgen_at_goal
        #[Syntax.atom .none "hax_mvcgen", cfgStx.raw, argStx,
          Syntax.atom .none "at", Syntax.atom .none "⊢"]⟩
    let goals ← evalTacticAt inner goal

    -- We partition the resulting goals into `newHypGoals` and `sideGoals`: If the conclusion
    -- of a goal is exactly `newHyp`, then we put it into `newHypGoals`, otherwise into `sideGoals`.
    let mut newHypGoals : Array MVarId := #[]
    let mut sideGoals : Array MVarId := #[]
    for goal in goals do
      let (_, goal) ← goal.withContext do goal.intros
      let target ← goal.withContext do instantiateMVars (← goal.getType)
      if target == newHyp then
        newHypGoals := newHypGoals.push goal
      else
        if (target.find? (· == newHyp)).isSome then
          Lean.Meta.throwTacticEx `hax_mvcgen mainGoal
            (m!"VC goal target contains but is not equal to the mvar: {target}")
        sideGoals := sideGoals.push goal

    -- For each `newHypGoal`, we collect the local decls `newFVars` that have been introduced
    -- by the `hax_mvcgen` call above.
    let mut newFVars : Array (Array Expr) := #[]
    for newHypGoal in newHypGoals do
      let lctx ← newHypGoal.withContext getLCtx
      let decls := (lctx.decls.toArray.drop previousLctxSize).filterMap id
      let fArgs := decls.map (mkFVar ·.fvarId)
      newFVars := newFVars.push fArgs

    -- For each newHypGoal `i`, build `newHypGoalProofsᵢ`:
    --   `fun (p : Prop) (f₁ : fType₁[p]) ... (fₙ : fTypeₙ[p]) => fᵢ newFVarsᵢ₁ ... newFVarsᵢₘ`
    -- where `fTypeⱼ` = `∀ newFVarsⱼ₁ ... newFVarsⱼₘ, p`
    -- All `newHypGoalProofs` have the same type: `∀ (p : Prop), fType₁ → ... → fTypeₙ → p`
    let mut newHypGoalProofs := #[]
    for i in [0:newHypGoals.size] do
      let newHypGoalProof ← newHypGoals[i]!.withContext do
        withLocalDeclD `p (mkSort .zero) fun p => do
          let fDeclsNamed ← (Array.range newFVars.size).mapM fun j => do
            let fType ← newHypGoals[j]!.withContext (mkForallFVars newFVars[j]! p)
            pure (Name.mkSimple s!"f{j + 1}", fun _ : Array Expr => pure fType)
          withLocalDeclsD fDeclsNamed fun fs => do
            mkLambdaFVars (#[p] ++ fs) (mkAppN fs[i]! newFVars[i]!)
      newHypGoalProofs := newHypGoalProofs.push newHypGoalProof

    -- Assign proofs to goals
    if !newHypGoals.isEmpty then
      newHyp.mvarId!.assign (← inferType newHypGoalProofs[0]!)
      for i in [0:newHypGoals.size] do
        newHypGoals[i]!.assign newHypGoalProofs[i]!
    else
      logWarning m!"hax_mvcgen at: no mvar VCs generated, only side conditions"

    -- Discharge side goals with `mvcgen`'s trivial discharger:
    let sideGoalsList ← sideGoals.toList.flatMapM
      fun sideGoal => do evalTacticAt (←  `(tactic| mvcgen_trivial)) sideGoal

    -- Replace old `hyp` with `newHyp`, using `newHypProof`.
    let {mvarId, fvarId, ..} ← mainGoal.replace hyp.fvarId (← mkLambdaFVars xs newHypProof)
    let mainGoals ←
      if xs.size == 0 then
        let r ← mvarId.apply (mkFVar fvarId)
        r.mapM (·.tryClear fvarId)
      else
        pure [mvarId]
    return (mainGoals ++ sideGoalsList)

syntax (name := hax_mvcgen_at_hyp) "hax_mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? "at" ident : tactic

@[tactic hax_mvcgen_at_hyp]
def elabHaxMvcgenAtHyp : Tactic := fun stx => do
  let cfgStx : TSyntax `Lean.Parser.Tactic.optConfig := ⟨stx[1]⟩
  let argStx := stx[2]
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let lctx ← getLCtx
    let .some hyp := lctx.findFromUserName? (Syntax.getId stx[4])
      | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Cannot find local assumption {stx[4]}")
    replaceMainGoal (← haxMvcgenAt mainGoal hyp cfgStx argStx)
