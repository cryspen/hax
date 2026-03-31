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

      if hbody.isForall then
        Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Why is this a forall???")

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


      --  `fun (p : Prop) (f : decl1.type -> decl2.type -> ... -> p) => f decl1.fvar decl2.fvar ...`.
      let mvarInsts ← goals.mapM fun goal => goal.withContext do
        let (_, goal) ← goal.intros
        goal.withContext do
          let lctx ← getLCtx
          withLocalDeclD `p (mkSort .zero) fun p => do
            let (fType, fArgs) ←
              lctx.foldrM
                fun decl (fType, fArgs) => do
                  logInfo m!"{decl.userName}"
                  if decl.index <= lastDecl.index
                  then pure (fType, fArgs)
                  else pure (← mkForallFVars #[mkFVar decl.fvarId] fType, (mkFVar decl.fvarId) :: fArgs)
                (p, [])
            logInfo m!"{fArgs}"
            withLocalDeclD `f fType fun f => do
              pure (goal, ← mkLambdaFVars #[p, f] (mkAppN f fArgs.toArray))

      logInfo m!"{mvarInsts}"
      let [(goal, mvarInst)] := mvarInsts
        | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"oops")
      -- TODO: Handle multiple VCs

      mvar.mvarId!.assign (← inferType mvarInst)
      goal.assign mvarInst

      let x ← mainGoal.replace h.fvarId (← mkLambdaFVars xs mvarGoal)
      setGoals [x.mvarId]

set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen at h
  apply True.intro


set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ∀ i, ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? i) ⦃ ⇓r => ⌜ r ⌝ ⦄) :  a + b > 0 := by
  hax_mvcgen at h
  apply h
  grind

set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do if ← (← a +? b) >? 0 then pure true else pure false) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen at h
  apply True.intro
