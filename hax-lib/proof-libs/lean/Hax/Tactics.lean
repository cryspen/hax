import Lean
import Qq
import Hax.Lib

open Lean Elab Tactic Meta Qq

macro "hax_bv_decide" c:Lean.Parser.Tactic.optConfig : tactic => `(tactic| (
  simp only [hax_bv_decide] at *; bv_decide $c
))

set_option trace.debug true

open Std.Do

def foldAnd : List Q(Prop) → Q(Prop)
| [] => q(True)
| [p] => p
| p :: ps => q($p ∧ $(foldAnd ps))

elab "hax_purify" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    have goalType : Q(Type) := goalDecl.type

    let p ←
      match goalType with
      | ~q(@Subtype.{0} _ $p) => pure p
      | ~q(@Subtype.{1} _ $p) => pure p
      | _ => Lean.Meta.throwTacticEx `hax_purify goal (m!"unable to run hax_purify on this goal: {goalType}")
    let p1 := p
    let (_, _, p) ← lambdaMetaTelescope p
    let (_, _, p) ← if p.isForall then forallMetaBoundedTelescope p 1 else pure (default, default, p)
    -- let #[v] := v
    --   | Lean.Meta.throwTacticEx `hax_purify goal (m!"expected exactly one lambda-variable: {v}")
    forallTelescope p fun vars (p : Q(Prop)) => do
      match p with
      | ~q(@Std.Do.Triple RustM _ _ Prop $condM _ _) => do

        let some lastGoalFVarId := (← getLCtx).getFVarIds.back?
          | Lean.Meta.throwTacticEx `hax_purify goal (m!"unexpected empty local context")

        if vars.size != 0 && vars.size != 1 then
          Lean.Meta.throwTacticEx `hax_purify goal (m!"expected either 0 or 1 forall-variables: {vars}")
        logInfo m!"{p}"
        -- let p ← if vars.size == 2 then mkLambdaFVars #[v] p else pure p
        logInfo m!"{p}"
        let mvcGoal ← mkFreshExprMVarQ q(⊢ₛ wp⟦$condM⟧ (⇓ r => ⌜r⌝))
        let vcs ← evalTacticAtRaw (← `(tactic| mvcgen)) (Expr.mvarId! mvcGoal)
        let wpcs ← vcs.mapM fun vc => do
          let decl ← vc.getDecl
          let hyps ← withLCtx decl.lctx decl.localInstances getLocalHyps
          let (_, x) ← vc.revertAfter lastGoalFVarId
          pure (← x.getDecl).type
        let wpc : Q(Prop) := foldAnd wpcs
        logInfo vars
        logInfo p1
        let wpc ← if vars.size == 1 then mkLambdaFVars vars wpc else pure wpc
        logInfo p1
        let xs ← goal.applyN (← mkAppOptM `Subtype.mk #[none, p1, wpc]) 1
        replaceMainGoal xs
        evalTactic (← `(tactic| intros))

      | _ => Lean.Meta.throwTacticEx `hax_purify goal (m!"expected triple, got: {p}")




def Playground.square.spec (x : u8)  :
    Spec
      (requires := (if x > 10 then pure (x == 15) else pure (x == 2)))
      (ensures := fun res => (if x > 10 then pure (x == res) else pure (x == 0)))
      (do pure (x : u8) : RustM _) := {
  pureRequires := by hax_purify <;> mvcgen <;> grind
  pureEnsures := by hax_purify <;> mvcgen <;> grind
  contract := by sorry
}
