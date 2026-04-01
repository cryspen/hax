import Lean
import Hax.core_models
import Hax.Tactic.HaxMvcgen

set_option autoImplicit true

open Lean
open Std.Do

theorem triple_in_hypothesis {f : RustM α} {Q : α → Assertion _} (p : Prop)
  (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
  (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
p := sorry

/-- For any `f` and postcondition `Q`, if `f` returns `r` satisfying `Q r`,
then `f` satisfies the noThrow triple with postcondition `Q`.
This holds for non-diverging `f` (which is guaranteed when the original triple is valid). -/
theorem wp_self_implication (f : RustM α) (Q : α → Assertion (.except Error .pure)) :
    ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => ⟨ (Q r).down → ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄ ⟩ ⦄ := by
  sorry

#check PostCond

-- @[specset int]
-- theorem haxAdd_spec {x y : u64} :
--     ⦃ ∀ r, spred(⌜ r.toNat = x.toNat + y.toNat ⌝ → Q.1 r) ⦄ (x +? y) ⦃ Q ⦄ := by sorry

@[specset int]
theorem haxAdd_spec {x y : u64} :
    ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓? r => ⌜ r.toNat = x.toNat + y.toNat ⌝ ⦄ := by sorry



open Elab Tactic Meta
set_option hygiene false in
elab "hax_mvcgen" "at" h:ident : tactic => do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let lctx ← getLCtx
    let .some h := lctx.findFromUserName? (Syntax.getId h)
      | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Cannot find local assumption {h}")

    forallTelescope (cleanupAnnotations := true) (← instantiateMVars h.type) fun xs hbody => do

      let .some lastDecl := (← getLCtx).findDeclRev? (fun decl => some decl)
        | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Unexpected empty local context")

      unless hbody.isAppOfArity' ``Triple 7 do
        Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Expected `Std.Do.Triple`, got {hbody}")
      let mvar ← mkFreshExprMVar (kind := .syntheticOpaque) (mkSort .zero)
      logInfo m!"hello {mvar}"
      let mvarGoal ← mkFreshExprMVar mvar
      let lemma ← mkAppM ``triple_in_hypothesis #[mvar, mkAppN (mkFVar h.fvarId) xs]
      let goals ← mvarGoal.mvarId!.apply lemma
      let [goal, _] := goals
        | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Unexpected number of goals after `triple_in_hypothesis`: {goals}")

      let goals ← evalTacticAt (←  `(tactic| hax_mvcgen -trivial)) goal


      -- Intro all goals and partition into mvar goals (target == mvar) and side-condition goals.
      -- For mvar goals, also collect `fTypeAbs` and `fArgs` for the CPS construction.
      let mut mvarVCs : Array (MVarId × Expr × List Expr) := #[]
      let mut sideGoals : Array MVarId := #[]
      for goal in goals do
        let (_, goal) ← goal.withContext do goal.intros
        let target ← goal.withContext do instantiateMVars (← goal.getType)
        if target == mvar then
          let vcInfo ← goal.withContext do
            let lctx ← getLCtx
            withLocalDeclD `p (mkSort .zero) fun p => do
              let (fType, fArgs) ←
                lctx.foldrM
                  fun decl (fType, fArgs) => do
                    if decl.index <= lastDecl.index
                    then pure (fType, fArgs)
                    else pure (← mkForallFVars #[mkFVar decl.fvarId] fType, (mkFVar decl.fvarId) :: fArgs)
                  (p, [])
              let fTypeAbs ← mkLambdaFVars #[p] fType
              pure (fTypeAbs, fArgs)

          mvarVCs := mvarVCs.push (goal, vcInfo.1, vcInfo.2)
        else
          if (target.find? (· == mvar)).isSome then
            Lean.Meta.throwTacticEx `hax_mvcgen mainGoal
              (m!"VC goal target contains but is not equal to the mvar: {target}")
          sideGoals := sideGoals.push goal

      if mvarVCs.isEmpty then
        logWarning m!"hax_mvcgen at: no mvar VCs generated, only side conditions"

      let allFTypeAbs := mvarVCs.map (·.2.1)

      -- For each mvar VC goal i, build:
      --   fun (p : Prop) (f₁ : fType₁[p]) ... (fₙ : fTypeₙ[p]) => fᵢ a_{i,1} ...
      -- Each goal uses only its i-th continuation fᵢ, but the lambda binds all of them.
      -- All mvarInsts have the same type: ∀ (p : Prop), fType₁ → ... → fTypeₙ → p
      let mvarInsts ← (Array.range mvarVCs.size).mapM fun idx => do
        let (goal, _, fArgs) := mvarVCs[idx]!
        let mvarInst ← goal.withContext do
          withLocalDeclD `p (mkSort .zero) fun p => do
            let fDeclsNamed := (Array.range allFTypeAbs.size).map fun i =>
              (Name.mkSimple s!"f{i + 1}", fun _ : Array Expr => pure (allFTypeAbs[i]!.beta #[p]))
            withLocalDeclsD fDeclsNamed fun fs => do
              mkLambdaFVars (#[p] ++ fs) (mkAppN fs[idx]! fArgs.toArray)
        pure (goal, mvarInst)

      logInfo m!"{mvarInsts.toList}"

      if !mvarVCs.isEmpty then
        mvar.mvarId!.assign (← inferType mvarInsts[0]!.2)
        for (goal, mvarInst) in mvarInsts.toList do
          goal.assign mvarInst

      let sideGoalsList ← sideGoals.toList.flatMapM
        fun sideGoal => do evalTacticAt (←  `(tactic| mvcgen_trivial)) sideGoal

      let x ← mainGoal.replace h.fvarId (← mkLambdaFVars xs mvarGoal)
      setGoals ([x.mvarId] ++ sideGoalsList)

-- A custom operation with no spec in any specset
def myOp (a b : u64) : RustM u64 := pure (a + b)

-- Example with an operation without spec
-- set_option hax_mvcgen.specset "int" in
-- example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← myOp a b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
--   hax_mvcgen at h
--   sorry

set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen at h
  apply True.intro


set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ∀ i, ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? i) ⦃ ⇓r => ⌜ r ⌝ ⦄) :  a + b > 0 := by
  hax_mvcgen at h
  apply h
  grind
  sorry

set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do if ← (← a +? b) >? 0 then pure true else pure false) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen at h
  apply True.intro
