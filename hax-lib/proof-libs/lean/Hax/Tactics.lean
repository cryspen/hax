import Lean
open Lean Elab Tactic



elab "split_and" : tactic => do
    Lean.Elab.Tactic.withMainContext do
      let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
      for decl in ctx do
        if let some _ := decl.type.and? then
          Lean.Elab.Tactic.evalTactic (← `(tactic| cases  $(mkIdent decl.userName):ident))
          return
      let goal ← Lean.Elab.Tactic.getMainGoal
      Lean.Meta.throwTacticEx `split_ands goal
        (m!"unable to find matching hypothesis of type _ ∧ _)")

elab "flatten" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| repeat split_and))
