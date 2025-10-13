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


macro "hax_bv_decide" : tactic => `(tactic| (
  any_goals (subst_vars ; injections ; subst_vars)
  all_goals try (
    simp [Int32.eq_iff_toBitVec_eq,
          Int32.lt_iff_toBitVec_slt,
          Int32.le_iff_toBitVec_sle,
          Int64.eq_iff_toBitVec_eq,
          Int64.lt_iff_toBitVec_slt,
          Int64.le_iff_toBitVec_sle] at * <;>
    bv_decide (config := {timeout := 1});
    done
 )))
