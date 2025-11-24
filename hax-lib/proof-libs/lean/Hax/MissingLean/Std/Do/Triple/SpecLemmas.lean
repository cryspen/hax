import Std.Do.Triple.Basic
import Hax.MissingLean.Init.While
import Hax.MissingLean.Std.Do.PostCond

namespace Std.Do
open Lean

@[spec]
theorem Spec.forIn_monoLoopCombinator {m} {ps : PostShape} {β: Type}
    [Monad m] [∀ α, Order.CCPO (m α)] [WPMonad m ps]
    (loop : Loop)
    (init : β)
    (f : Unit → β → m (ForInStep β)) [Loop.MonoLoopCombinator f]
    (inv : PostCond β ps)
    (termination : β -> Nat)
    (step : ∀ b,
      ⦃inv.1 b⦄
        f () b
      ⦃(fun r => match r with
        | .yield b' => spred(⌜ termination b' < termination b ⌝ ∧ inv.1 b')
        | .done b' => inv.1 b', inv.2)⦄) :
    ⦃inv.1 init⦄ Loop.MonoLoopCombinator.forIn loop init f ⦃(fun b => inv.1 b, inv.2)⦄ := by
  unfold Loop.MonoLoopCombinator.forIn Loop.MonoLoopCombinator.forIn.loop Loop.loopCombinator
  apply Triple.bind
  · apply step
  · rintro (b | b)
    · refine Triple.pure b ?_
      exact SPred.entails.refl (inv.fst b)
    · apply SPred.imp_elim
      apply SPred.pure_elim'
      intro h
      rw [SPred.entails_true_intro]
      apply Spec.forIn_monoLoopCombinator loop _ f inv termination step
termination_by termination init
decreasing_by exact h

@[spec]
theorem Spec.MonoLoopCombinator.while_loop {m} {ps : PostShape} {β: Type}
    [Monad m] [∀ α, Order.CCPO (m α)] [WPMonad m ps]
    [∀ f : Unit → β → m (ForInStep β), Loop.MonoLoopCombinator f]
    (init : β)
    (loop : Loop)
    (cond: β → m Bool)
    (body : β → m β)
    (inv: β → Prop)
    (termination : β → Nat)
    (step :
      ∀ (b : β),
        ⦃⌜ inv b ⌝⦄
          do
            if ← cond b
            then return ForInStep.yield (← body b)
            else return ForInStep.done b
        ⦃(fun r =>
          match r with
          | ForInStep.yield b' => spred(⌜ termination b' < termination b ⌝ ∧ ⌜ inv b' ⌝)
          | ForInStep.done b' => ⌜ inv b' ⌝,
          ExceptConds.false)⦄ ) :
    ⦃⌜ inv init ⌝⦄
      Loop.MonoLoopCombinator.while_loop loop cond init body
    ⦃⇓ b => ⌜ inv b ⌝⦄ := by
  apply Spec.forIn_monoLoopCombinator
    (inv := (fun b => ⌜ inv b ⌝ , ExceptConds.false))
    (step := step)
