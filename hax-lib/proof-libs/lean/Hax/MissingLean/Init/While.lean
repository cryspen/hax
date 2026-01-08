import Std.Do

namespace Lean

open Order
open Std.Do

universe u v

/-- Runs one iteration of a loop and continues with `l`. -/
def Loop.loopCombinator {β : Type u} {m : Type u → Type v} [Monad m]
    (f : Unit → β → m (ForInStep β)) (l : β → m β) (b : β) := do
  match ← f () b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => l b

/-- A monad function must implement this type class to be able to use loops based on
`partial_fixpoint`. -/
class Loop.MonoLoopCombinator
    {β : Type u} {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)]
    (f : Unit → β → m (ForInStep β)) where
  mono : monotone (loopCombinator f) := by unfold Lean.Loop.loopCombinator <;> monotonicity

/-- Our own copy of `Loop.forIn` because the original one is `partial` and thus we cannot reason
about it. -/
@[inline]
def Loop.MonoLoopCombinator.forIn {β : Type u} {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)]
    (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) [MonoLoopCombinator f] :
    m β :=
  let rec @[specialize] loop [MonoLoopCombinator f] (b : β) : m β :=
    loopCombinator f loop b
  partial_fixpoint monotonicity MonoLoopCombinator.mono
  loop init

/-- A while loop based on `Loop.MonoLoopCombinator.forIn`. -/
def Loop.MonoLoopCombinator.while_loop  {m} {ps : PostShape} {β: Type}
    [Monad m] [∀ α, Order.CCPO (m α)] [WPMonad m ps]
    (loop : Loop)
    (cond: β → Bool)
    (init : β)
    (body : β -> m β)
    [∀ f : Unit → β → m (ForInStep β), Loop.MonoLoopCombinator f] : m β :=
  Loop.MonoLoopCombinator.forIn loop init fun () s => do
    if cond s then
      let s ← body s
      pure (.yield s)
    else
      pure (.done s)

end Lean
