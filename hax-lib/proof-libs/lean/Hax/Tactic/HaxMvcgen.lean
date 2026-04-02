import Hax.Tactic.HaxMvcgenAt
import Hax.Tactic.HaxMvcgenAtGoal

set_option autoImplicit true

open Lean Std.Do Elab Parser Tactic Meta

private def isTripleExpr (e : Expr) : MetaM Bool := do
  forallTelescope (cleanupAnnotations := true) (← instantiateMVars e) fun _ body =>
    return (← whnfR body).isAppOfArity' ``Triple 7

partial def haxMvcgenLoop (mainGoal : MVarId)
    (cfgStx : TSyntax `Lean.Parser.Tactic.optConfig) (argStx : Syntax) :
    TacticM (List MVarId) := do
  let (_, mainGoal) ← mainGoal.intros
  mainGoal.withContext do
    let goalType ← whnfR (← instantiateMVars (← mainGoal.getType))
    if goalType.isAppOfArity' ``Triple 7 then
      logInfo m!"hax_mvcgen at ⊢: {mainGoal}"
      let inner : TSyntax `tactic := ⟨Syntax.node .none ``Hax.HaxMvcgen.hax_mvcgen_at_goal
        #[Syntax.atom .none "hax_mvcgen", cfgStx.raw, argStx,
          Syntax.atom .none "at", Syntax.atom .none "⊢"]⟩
      let goals ← evalTacticAt inner mainGoal
      return (← goals.flatMapM (haxMvcgenLoop · cfgStx argStx))
    let lctx ← getLCtx
    for hyp in lctx.decls.toArray.filterMap id do
      if !hyp.isImplementationDetail && (← isTripleExpr hyp.type) then
        logInfo m!"hax_mvcgen at {hyp.userName}: {hyp.type}"
        let goals ← haxMvcgenAt mainGoal hyp cfgStx argStx
        return (← goals.flatMapM (haxMvcgenLoop · cfgStx argStx))
    return [mainGoal]

syntax (name := hax_mvcgen) "hax_mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic hax_mvcgen]
def elabHaxMvcgenLoop : Tactic := fun stx => do
  let cfgStx : TSyntax `Lean.Parser.Tactic.optConfig := ⟨stx[1]⟩
  let argStx := stx[2]
  replaceMainGoal (← haxMvcgenLoop (← getMainGoal) cfgStx argStx)
