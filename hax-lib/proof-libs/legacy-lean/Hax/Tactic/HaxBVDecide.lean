import Std.Tactic.BVDecide

macro "hax_bv_decide" c:Lean.Parser.Tactic.optConfig : tactic => `(tactic| (
  simp only [hax_bv_decide] at *; bv_decide $c
))
