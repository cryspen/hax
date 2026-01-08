import Std.Do.Triple.Basic
import Hax.MissingLean.Std.Do.Triple.Basic
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
    (inv : β → Prop)
    (termination : β -> Nat)
    (post : β → Prop)
    (step : ∀ b,
      ⦃⌜ inv b ⌝⦄
        f () b
      ⦃⇓ r => match r with
        | .yield b' => spred(⌜ termination b' < termination b ⌝ ∧ ⌜ inv b' ⌝)
        | .done b' => ⌜ post b' ⌝⦄) :
    ⦃⌜ inv init ⌝⦄ Loop.MonoLoopCombinator.forIn loop init f ⦃⇓ b => ⌜ post b ⌝⦄ := by
  unfold Loop.MonoLoopCombinator.forIn Loop.MonoLoopCombinator.forIn.loop Loop.loopCombinator
  apply Triple.bind
  · apply step
  · rintro (b | b)
    · refine Triple.pure b ?_
      exact SPred.entails.refl _
    · apply SPred.imp_elim
      apply SPred.pure_elim'
      intro h
      rw [SPred.entails_true_intro]
      apply Spec.forIn_monoLoopCombinator loop _ f inv termination post step
termination_by termination init
decreasing_by exact h

@[spec]
theorem Spec.MonoLoopCombinator.while_loop {m} {ps : PostShape} {β: Type}
    [Monad m] [∀ α, Order.CCPO (m α)] [WPMonad m ps]
    [∀ f : Unit → β → m (ForInStep β), Loop.MonoLoopCombinator f]
    (init : β)
    (loop : Loop)
    (cond: β → Bool)
    (body : β → m β)
    (inv: β → Prop)
    (termination : β → Nat)
    (step :
      ∀ (b : β), cond b →
        ⦃⌜ inv b ⌝⦄
          body b
        ⦃⇓ b' => spred(⌜ termination b' < termination b ⌝ ∧ ⌜ inv b' ⌝)⦄ ) :
    ⦃⌜ inv init ⌝⦄
      Loop.MonoLoopCombinator.while_loop loop cond init body
    ⦃⇓ b => ⌜ inv b ∧ ¬ cond b ⌝⦄ := by
  apply Spec.forIn_monoLoopCombinator
  intro b
  by_cases hb : cond b
  · simpa [hb, Triple.map] using step b hb
  · simp [hb, Triple.pure]
