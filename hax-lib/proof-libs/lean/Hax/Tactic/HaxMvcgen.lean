import Hax.Tactic.HaxMvcgenAt
import Hax.Tactic.HaxMvcgenAtGoal

set_option autoImplicit true

open Lean Std.Do Elab Tactic Meta

private def isTripleExpr (e : Expr) : MetaM Bool := do
  forallTelescope (cleanupAnnotations := true) (← instantiateMVars e) fun _ body =>
    return (← whnfR body).isAppOfArity' ``Triple 7

partial def haxMvcgenLoop (mainGoal : MVarId) : TacticM (List MVarId) := do
  let (_, mainGoal) ← mainGoal.intros
  mainGoal.withContext do
    let goalType ← whnfR (← instantiateMVars (← mainGoal.getType))
    if goalType.isAppOfArity' ``Triple 7 then
      logInfo m!"hax_mvcgen at ⊢: {mainGoal}"
      let goals ← evalTacticAt (← `(tactic| hax_mvcgen at ⊢)) mainGoal
      return (← goals.flatMapM haxMvcgenLoop)
    let lctx ← getLCtx
    for hyp in lctx.decls.toArray.filterMap id do
      if !hyp.isImplementationDetail && (← isTripleExpr hyp.type) then
        logInfo m!"hax_mvcgen at {hyp.userName}: {hyp.type}"
        let goals ← haxMvcgenAt mainGoal hyp {}
        return (← goals.flatMapM haxMvcgenLoop)
    return [mainGoal]

syntax (name := hax_mvcgen) "hax_mvcgen" : tactic

@[tactic hax_mvcgen]
def elabHaxMvcgenLoop : Tactic := fun _ => do
  replaceMainGoal (← haxMvcgenLoop (← getMainGoal))
