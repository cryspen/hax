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
    unless h.type.isAppOfArity' ``Triple 7 do
      Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Expected `Std.Do.Triple`, got {h.type}")
    let mvar ← mkFreshExprMVar (kind := .syntheticOpaque) (mkSort .zero)
    logInfo m!"hello {mvar}"
    let mvarGoal ← mkFreshExprMVar mvar
    let lemma ← mkAppM ``triple_in_hypothesis #[mvar, mkFVar h.fvarId]
    let goals ← mvarGoal.mvarId!.apply lemma
    let [goal, _] := goals
      | Lean.Meta.throwTacticEx `hax_mvcgen mainGoal (m!"Unexpected number of goals after `triple_in_hypothesis`: {goals}")

    let goals ← evalTacticAt (←  `(tactic| hax_mvcgen -trivial)) goal

    let [goal] := goals
      | Lean.Meta.throwTacticEx `hax_mvcgen goal (m!"Cannot handle multiple VCs: {goals}")
    let (_, goal) ← goal.intros

    let .some lastDecl := lctx.findDeclRev? (fun decl => some decl)
      | Lean.Meta.throwTacticEx `hax_mvcgen goal (m!"Unexpected empty local context")

    logInfo m!"{goal}"

    goal.withContext do
      let lctx ← getLCtx
      let mvarInst ← lctx.foldrM
        fun decl acc => do
          if decl.index <= lastDecl.index
          then pure acc
          else if (← inferType decl.type).isProp then
            if acc.isAppOf ``True.intro then
              pure (mkFVar decl.fvarId)
            else
              pure (← mkAppM ``And.intro #[
                mkFVar decl.fvarId,
                acc])
          else
            pure (← mkAppOptM ``Exists.intro #[
              decl.type,
              ← mkLambdaFVars #[mkFVar decl.fvarId] (← inferType acc),
              mkFVar decl.fvarId,
              acc])
        (mkConst ``True.intro)
      logInfo mvarInst
      goal.assign mvarInst
      mvarGoal.mvarId!.assign mvarInst
      mvar.mvarId!.assign (← inferType mvarInst)

      let x ← mainGoal.replace h.fvarId mvarGoal
      setGoals [x.mvarId]

set_option hax_mvcgen.specset "int"
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen at h
  apply True.intro
